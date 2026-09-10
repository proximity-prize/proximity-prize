import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked02

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_3_0_0 : CertificateAt 3 0 0 := by decide +kernel
theorem cell_3_0_1 : CertificateAt 3 0 1 := by decide +kernel
theorem cell_3_0_2 : CertificateAt 3 0 2 := by decide +kernel
theorem cell_3_0_3 : CertificateAt 3 0 3 := by decide +kernel
theorem cell_3_0_4 : CertificateAt 3 0 4 := by decide +kernel
theorem cell_3_0_5 : CertificateAt 3 0 5 := by decide +kernel
theorem row_3_0 : ThresholdAt 3 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 0 0 cell_3_0_0
    | exact certificate_sound 3 0 1 cell_3_0_1
    | exact certificate_sound 3 0 2 cell_3_0_2
    | exact certificate_sound 3 0 3 cell_3_0_3
    | exact certificate_sound 3 0 4 cell_3_0_4
    | exact certificate_sound 3 0 5 cell_3_0_5
theorem cell_3_1_0 : CertificateAt 3 1 0 := by decide +kernel
theorem cell_3_1_1 : CertificateAt 3 1 1 := by decide +kernel
theorem cell_3_1_2 : CertificateAt 3 1 2 := by decide +kernel
theorem cell_3_1_3 : CertificateAt 3 1 3 := by decide +kernel
theorem cell_3_1_4 : CertificateAt 3 1 4 := by decide +kernel
theorem cell_3_1_5 : CertificateAt 3 1 5 := by decide +kernel
theorem row_3_1 : ThresholdAt 3 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 1 0 cell_3_1_0
    | exact certificate_sound 3 1 1 cell_3_1_1
    | exact certificate_sound 3 1 2 cell_3_1_2
    | exact certificate_sound 3 1 3 cell_3_1_3
    | exact certificate_sound 3 1 4 cell_3_1_4
    | exact certificate_sound 3 1 5 cell_3_1_5
theorem cell_3_2_0 : CertificateAt 3 2 0 := by decide +kernel
theorem cell_3_2_1 : CertificateAt 3 2 1 := by decide +kernel
theorem cell_3_2_2 : CertificateAt 3 2 2 := by decide +kernel
theorem cell_3_2_3 : CertificateAt 3 2 3 := by decide +kernel
theorem cell_3_2_4 : CertificateAt 3 2 4 := by decide +kernel
theorem cell_3_2_5 : CertificateAt 3 2 5 := by decide +kernel
theorem row_3_2 : ThresholdAt 3 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 2 0 cell_3_2_0
    | exact certificate_sound 3 2 1 cell_3_2_1
    | exact certificate_sound 3 2 2 cell_3_2_2
    | exact certificate_sound 3 2 3 cell_3_2_3
    | exact certificate_sound 3 2 4 cell_3_2_4
    | exact certificate_sound 3 2 5 cell_3_2_5
theorem cell_3_3_0 : CertificateAt 3 3 0 := by decide +kernel
theorem cell_3_3_1 : CertificateAt 3 3 1 := by decide +kernel
theorem cell_3_3_2 : CertificateAt 3 3 2 := by decide +kernel
theorem cell_3_3_3 : CertificateAt 3 3 3 := by decide +kernel
theorem cell_3_3_4 : CertificateAt 3 3 4 := by decide +kernel
theorem cell_3_3_5 : CertificateAt 3 3 5 := by decide +kernel
theorem row_3_3 : ThresholdAt 3 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 3 0 cell_3_3_0
    | exact certificate_sound 3 3 1 cell_3_3_1
    | exact certificate_sound 3 3 2 cell_3_3_2
    | exact certificate_sound 3 3 3 cell_3_3_3
    | exact certificate_sound 3 3 4 cell_3_3_4
    | exact certificate_sound 3 3 5 cell_3_3_5
theorem cell_3_4_0 : CertificateAt 3 4 0 := by decide +kernel
theorem cell_3_4_1 : CertificateAt 3 4 1 := by decide +kernel
theorem cell_3_4_2 : CertificateAt 3 4 2 := by decide +kernel
theorem cell_3_4_3 : CertificateAt 3 4 3 := by decide +kernel
theorem cell_3_4_4 : CertificateAt 3 4 4 := by decide +kernel
theorem cell_3_4_5 : CertificateAt 3 4 5 := by decide +kernel
theorem row_3_4 : ThresholdAt 3 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 4 0 cell_3_4_0
    | exact certificate_sound 3 4 1 cell_3_4_1
    | exact certificate_sound 3 4 2 cell_3_4_2
    | exact certificate_sound 3 4 3 cell_3_4_3
    | exact certificate_sound 3 4 4 cell_3_4_4
    | exact certificate_sound 3 4 5 cell_3_4_5
theorem cell_3_5_0 : CertificateAt 3 5 0 := by decide +kernel
theorem cell_3_5_1 : CertificateAt 3 5 1 := by decide +kernel
theorem cell_3_5_2 : CertificateAt 3 5 2 := by decide +kernel
theorem cell_3_5_3 : CertificateAt 3 5 3 := by decide +kernel
theorem cell_3_5_4 : CertificateAt 3 5 4 := by decide +kernel
theorem cell_3_5_5 : CertificateAt 3 5 5 := by decide +kernel
theorem row_3_5 : ThresholdAt 3 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 5 0 cell_3_5_0
    | exact certificate_sound 3 5 1 cell_3_5_1
    | exact certificate_sound 3 5 2 cell_3_5_2
    | exact certificate_sound 3 5 3 cell_3_5_3
    | exact certificate_sound 3 5 4 cell_3_5_4
    | exact certificate_sound 3 5 5 cell_3_5_5
theorem cell_3_6_0 : CertificateAt 3 6 0 := by decide +kernel
theorem cell_3_6_1 : CertificateAt 3 6 1 := by decide +kernel
theorem cell_3_6_2 : CertificateAt 3 6 2 := by decide +kernel
theorem cell_3_6_3 : CertificateAt 3 6 3 := by decide +kernel
theorem cell_3_6_4 : CertificateAt 3 6 4 := by decide +kernel
theorem cell_3_6_5 : CertificateAt 3 6 5 := by decide +kernel
theorem row_3_6 : ThresholdAt 3 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 6 0 cell_3_6_0
    | exact certificate_sound 3 6 1 cell_3_6_1
    | exact certificate_sound 3 6 2 cell_3_6_2
    | exact certificate_sound 3 6 3 cell_3_6_3
    | exact certificate_sound 3 6 4 cell_3_6_4
    | exact certificate_sound 3 6 5 cell_3_6_5
theorem cell_3_7_0 : CertificateAt 3 7 0 := by decide +kernel
theorem cell_3_7_1 : CertificateAt 3 7 1 := by decide +kernel
theorem cell_3_7_2 : CertificateAt 3 7 2 := by decide +kernel
theorem cell_3_7_3 : CertificateAt 3 7 3 := by decide +kernel
theorem cell_3_7_4 : CertificateAt 3 7 4 := by decide +kernel
theorem cell_3_7_5 : CertificateAt 3 7 5 := by decide +kernel
theorem row_3_7 : ThresholdAt 3 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 7 0 cell_3_7_0
    | exact certificate_sound 3 7 1 cell_3_7_1
    | exact certificate_sound 3 7 2 cell_3_7_2
    | exact certificate_sound 3 7 3 cell_3_7_3
    | exact certificate_sound 3 7 4 cell_3_7_4
    | exact certificate_sound 3 7 5 cell_3_7_5
theorem cell_3_8_0 : CertificateAt 3 8 0 := by decide +kernel
theorem cell_3_8_1 : CertificateAt 3 8 1 := by decide +kernel
theorem cell_3_8_2 : CertificateAt 3 8 2 := by decide +kernel
theorem cell_3_8_3 : CertificateAt 3 8 3 := by decide +kernel
theorem cell_3_8_4 : CertificateAt 3 8 4 := by decide +kernel
theorem cell_3_8_5 : CertificateAt 3 8 5 := by decide +kernel
theorem row_3_8 : ThresholdAt 3 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 8 0 cell_3_8_0
    | exact certificate_sound 3 8 1 cell_3_8_1
    | exact certificate_sound 3 8 2 cell_3_8_2
    | exact certificate_sound 3 8 3 cell_3_8_3
    | exact certificate_sound 3 8 4 cell_3_8_4
    | exact certificate_sound 3 8 5 cell_3_8_5
theorem cell_3_9_0 : CertificateAt 3 9 0 := by decide +kernel
theorem cell_3_9_1 : CertificateAt 3 9 1 := by decide +kernel
theorem cell_3_9_2 : CertificateAt 3 9 2 := by decide +kernel
theorem cell_3_9_3 : CertificateAt 3 9 3 := by decide +kernel
theorem cell_3_9_4 : CertificateAt 3 9 4 := by decide +kernel
theorem cell_3_9_5 : CertificateAt 3 9 5 := by decide +kernel
theorem row_3_9 : ThresholdAt 3 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 9 0 cell_3_9_0
    | exact certificate_sound 3 9 1 cell_3_9_1
    | exact certificate_sound 3 9 2 cell_3_9_2
    | exact certificate_sound 3 9 3 cell_3_9_3
    | exact certificate_sound 3 9 4 cell_3_9_4
    | exact certificate_sound 3 9 5 cell_3_9_5
theorem cell_3_10_0 : CertificateAt 3 10 0 := by decide +kernel
theorem cell_3_10_1 : CertificateAt 3 10 1 := by decide +kernel
theorem cell_3_10_2 : CertificateAt 3 10 2 := by decide +kernel
theorem cell_3_10_3 : CertificateAt 3 10 3 := by decide +kernel
theorem cell_3_10_4 : CertificateAt 3 10 4 := by decide +kernel
theorem cell_3_10_5 : CertificateAt 3 10 5 := by decide +kernel
theorem row_3_10 : ThresholdAt 3 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 10 0 cell_3_10_0
    | exact certificate_sound 3 10 1 cell_3_10_1
    | exact certificate_sound 3 10 2 cell_3_10_2
    | exact certificate_sound 3 10 3 cell_3_10_3
    | exact certificate_sound 3 10 4 cell_3_10_4
    | exact certificate_sound 3 10 5 cell_3_10_5
theorem cell_3_11_0 : CertificateAt 3 11 0 := by decide +kernel
theorem cell_3_11_1 : CertificateAt 3 11 1 := by decide +kernel
theorem cell_3_11_2 : CertificateAt 3 11 2 := by decide +kernel
theorem cell_3_11_3 : CertificateAt 3 11 3 := by decide +kernel
theorem cell_3_11_4 : CertificateAt 3 11 4 := by decide +kernel
theorem cell_3_11_5 : CertificateAt 3 11 5 := by decide +kernel
theorem row_3_11 : ThresholdAt 3 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 11 0 cell_3_11_0
    | exact certificate_sound 3 11 1 cell_3_11_1
    | exact certificate_sound 3 11 2 cell_3_11_2
    | exact certificate_sound 3 11 3 cell_3_11_3
    | exact certificate_sound 3 11 4 cell_3_11_4
    | exact certificate_sound 3 11 5 cell_3_11_5
theorem cell_3_12_0 : CertificateAt 3 12 0 := by decide +kernel
theorem cell_3_12_1 : CertificateAt 3 12 1 := by decide +kernel
theorem cell_3_12_2 : CertificateAt 3 12 2 := by decide +kernel
theorem cell_3_12_3 : CertificateAt 3 12 3 := by decide +kernel
theorem cell_3_12_4 : CertificateAt 3 12 4 := by decide +kernel
theorem cell_3_12_5 : CertificateAt 3 12 5 := by decide +kernel
theorem row_3_12 : ThresholdAt 3 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 12 0 cell_3_12_0
    | exact certificate_sound 3 12 1 cell_3_12_1
    | exact certificate_sound 3 12 2 cell_3_12_2
    | exact certificate_sound 3 12 3 cell_3_12_3
    | exact certificate_sound 3 12 4 cell_3_12_4
    | exact certificate_sound 3 12 5 cell_3_12_5
theorem cell_3_13_0 : CertificateAt 3 13 0 := by decide +kernel
theorem cell_3_13_1 : CertificateAt 3 13 1 := by decide +kernel
theorem cell_3_13_2 : CertificateAt 3 13 2 := by decide +kernel
theorem cell_3_13_3 : CertificateAt 3 13 3 := by decide +kernel
theorem cell_3_13_4 : CertificateAt 3 13 4 := by decide +kernel
theorem cell_3_13_5 : CertificateAt 3 13 5 := by decide +kernel
theorem row_3_13 : ThresholdAt 3 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 13 0 cell_3_13_0
    | exact certificate_sound 3 13 1 cell_3_13_1
    | exact certificate_sound 3 13 2 cell_3_13_2
    | exact certificate_sound 3 13 3 cell_3_13_3
    | exact certificate_sound 3 13 4 cell_3_13_4
    | exact certificate_sound 3 13 5 cell_3_13_5
theorem cell_3_14_0 : CertificateAt 3 14 0 := by decide +kernel
theorem cell_3_14_1 : CertificateAt 3 14 1 := by decide +kernel
theorem cell_3_14_2 : CertificateAt 3 14 2 := by decide +kernel
theorem cell_3_14_3 : CertificateAt 3 14 3 := by decide +kernel
theorem cell_3_14_4 : CertificateAt 3 14 4 := by decide +kernel
theorem cell_3_14_5 : CertificateAt 3 14 5 := by decide +kernel
theorem row_3_14 : ThresholdAt 3 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 14 0 cell_3_14_0
    | exact certificate_sound 3 14 1 cell_3_14_1
    | exact certificate_sound 3 14 2 cell_3_14_2
    | exact certificate_sound 3 14 3 cell_3_14_3
    | exact certificate_sound 3 14 4 cell_3_14_4
    | exact certificate_sound 3 14 5 cell_3_14_5
theorem cell_3_15_0 : CertificateAt 3 15 0 := by decide +kernel
theorem cell_3_15_1 : CertificateAt 3 15 1 := by decide +kernel
theorem cell_3_15_2 : CertificateAt 3 15 2 := by decide +kernel
theorem cell_3_15_3 : CertificateAt 3 15 3 := by decide +kernel
theorem cell_3_15_4 : CertificateAt 3 15 4 := by decide +kernel
theorem cell_3_15_5 : CertificateAt 3 15 5 := by decide +kernel
theorem row_3_15 : ThresholdAt 3 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 15 0 cell_3_15_0
    | exact certificate_sound 3 15 1 cell_3_15_1
    | exact certificate_sound 3 15 2 cell_3_15_2
    | exact certificate_sound 3 15 3 cell_3_15_3
    | exact certificate_sound 3 15 4 cell_3_15_4
    | exact certificate_sound 3 15 5 cell_3_15_5
theorem cell_3_16_0 : CertificateAt 3 16 0 := by decide +kernel
theorem cell_3_16_1 : CertificateAt 3 16 1 := by decide +kernel
theorem cell_3_16_2 : CertificateAt 3 16 2 := by decide +kernel
theorem cell_3_16_3 : CertificateAt 3 16 3 := by decide +kernel
theorem cell_3_16_4 : CertificateAt 3 16 4 := by decide +kernel
theorem cell_3_16_5 : CertificateAt 3 16 5 := by decide +kernel
theorem row_3_16 : ThresholdAt 3 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 16 0 cell_3_16_0
    | exact certificate_sound 3 16 1 cell_3_16_1
    | exact certificate_sound 3 16 2 cell_3_16_2
    | exact certificate_sound 3 16 3 cell_3_16_3
    | exact certificate_sound 3 16 4 cell_3_16_4
    | exact certificate_sound 3 16 5 cell_3_16_5
theorem cell_3_17_0 : CertificateAt 3 17 0 := by decide +kernel
theorem cell_3_17_1 : CertificateAt 3 17 1 := by decide +kernel
theorem cell_3_17_2 : CertificateAt 3 17 2 := by decide +kernel
theorem cell_3_17_3 : CertificateAt 3 17 3 := by decide +kernel
theorem cell_3_17_4 : CertificateAt 3 17 4 := by decide +kernel
theorem cell_3_17_5 : CertificateAt 3 17 5 := by decide +kernel
theorem row_3_17 : ThresholdAt 3 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 17 0 cell_3_17_0
    | exact certificate_sound 3 17 1 cell_3_17_1
    | exact certificate_sound 3 17 2 cell_3_17_2
    | exact certificate_sound 3 17 3 cell_3_17_3
    | exact certificate_sound 3 17 4 cell_3_17_4
    | exact certificate_sound 3 17 5 cell_3_17_5
theorem cell_3_18_0 : CertificateAt 3 18 0 := by decide +kernel
theorem cell_3_18_1 : CertificateAt 3 18 1 := by decide +kernel
theorem cell_3_18_2 : CertificateAt 3 18 2 := by decide +kernel
theorem cell_3_18_3 : CertificateAt 3 18 3 := by decide +kernel
theorem cell_3_18_4 : CertificateAt 3 18 4 := by decide +kernel
theorem cell_3_18_5 : CertificateAt 3 18 5 := by decide +kernel
theorem row_3_18 : ThresholdAt 3 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 18 0 cell_3_18_0
    | exact certificate_sound 3 18 1 cell_3_18_1
    | exact certificate_sound 3 18 2 cell_3_18_2
    | exact certificate_sound 3 18 3 cell_3_18_3
    | exact certificate_sound 3 18 4 cell_3_18_4
    | exact certificate_sound 3 18 5 cell_3_18_5
theorem cell_3_19_0 : CertificateAt 3 19 0 := by decide +kernel
theorem cell_3_19_1 : CertificateAt 3 19 1 := by decide +kernel
theorem cell_3_19_2 : CertificateAt 3 19 2 := by decide +kernel
theorem cell_3_19_3 : CertificateAt 3 19 3 := by decide +kernel
theorem cell_3_19_4 : CertificateAt 3 19 4 := by decide +kernel
theorem cell_3_19_5 : CertificateAt 3 19 5 := by decide +kernel
theorem row_3_19 : ThresholdAt 3 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 19 0 cell_3_19_0
    | exact certificate_sound 3 19 1 cell_3_19_1
    | exact certificate_sound 3 19 2 cell_3_19_2
    | exact certificate_sound 3 19 3 cell_3_19_3
    | exact certificate_sound 3 19 4 cell_3_19_4
    | exact certificate_sound 3 19 5 cell_3_19_5
theorem cell_3_20_0 : CertificateAt 3 20 0 := by decide +kernel
theorem cell_3_20_1 : CertificateAt 3 20 1 := by decide +kernel
theorem cell_3_20_2 : CertificateAt 3 20 2 := by decide +kernel
theorem cell_3_20_3 : CertificateAt 3 20 3 := by decide +kernel
theorem cell_3_20_4 : CertificateAt 3 20 4 := by decide +kernel
theorem cell_3_20_5 : CertificateAt 3 20 5 := by decide +kernel
theorem row_3_20 : ThresholdAt 3 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 20 0 cell_3_20_0
    | exact certificate_sound 3 20 1 cell_3_20_1
    | exact certificate_sound 3 20 2 cell_3_20_2
    | exact certificate_sound 3 20 3 cell_3_20_3
    | exact certificate_sound 3 20 4 cell_3_20_4
    | exact certificate_sound 3 20 5 cell_3_20_5
theorem cell_3_21_0 : CertificateAt 3 21 0 := by decide +kernel
theorem cell_3_21_1 : CertificateAt 3 21 1 := by decide +kernel
theorem cell_3_21_2 : CertificateAt 3 21 2 := by decide +kernel
theorem cell_3_21_3 : CertificateAt 3 21 3 := by decide +kernel
theorem cell_3_21_4 : CertificateAt 3 21 4 := by decide +kernel
theorem cell_3_21_5 : CertificateAt 3 21 5 := by decide +kernel
theorem row_3_21 : ThresholdAt 3 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 21 0 cell_3_21_0
    | exact certificate_sound 3 21 1 cell_3_21_1
    | exact certificate_sound 3 21 2 cell_3_21_2
    | exact certificate_sound 3 21 3 cell_3_21_3
    | exact certificate_sound 3 21 4 cell_3_21_4
    | exact certificate_sound 3 21 5 cell_3_21_5
theorem cell_3_22_0 : CertificateAt 3 22 0 := by decide +kernel
theorem cell_3_22_1 : CertificateAt 3 22 1 := by decide +kernel
theorem cell_3_22_2 : CertificateAt 3 22 2 := by decide +kernel
theorem cell_3_22_3 : CertificateAt 3 22 3 := by decide +kernel
theorem cell_3_22_4 : CertificateAt 3 22 4 := by decide +kernel
theorem cell_3_22_5 : CertificateAt 3 22 5 := by decide +kernel
theorem row_3_22 : ThresholdAt 3 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 22 0 cell_3_22_0
    | exact certificate_sound 3 22 1 cell_3_22_1
    | exact certificate_sound 3 22 2 cell_3_22_2
    | exact certificate_sound 3 22 3 cell_3_22_3
    | exact certificate_sound 3 22 4 cell_3_22_4
    | exact certificate_sound 3 22 5 cell_3_22_5
theorem cell_3_23_0 : CertificateAt 3 23 0 := by decide +kernel
theorem cell_3_23_1 : CertificateAt 3 23 1 := by decide +kernel
theorem cell_3_23_2 : CertificateAt 3 23 2 := by decide +kernel
theorem cell_3_23_3 : CertificateAt 3 23 3 := by decide +kernel
theorem cell_3_23_4 : CertificateAt 3 23 4 := by decide +kernel
theorem cell_3_23_5 : CertificateAt 3 23 5 := by decide +kernel
theorem row_3_23 : ThresholdAt 3 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 23 0 cell_3_23_0
    | exact certificate_sound 3 23 1 cell_3_23_1
    | exact certificate_sound 3 23 2 cell_3_23_2
    | exact certificate_sound 3 23 3 cell_3_23_3
    | exact certificate_sound 3 23 4 cell_3_23_4
    | exact certificate_sound 3 23 5 cell_3_23_5
theorem cell_3_24_0 : CertificateAt 3 24 0 := by decide +kernel
theorem cell_3_24_1 : CertificateAt 3 24 1 := by decide +kernel
theorem cell_3_24_2 : CertificateAt 3 24 2 := by decide +kernel
theorem cell_3_24_3 : CertificateAt 3 24 3 := by decide +kernel
theorem cell_3_24_4 : CertificateAt 3 24 4 := by decide +kernel
theorem cell_3_24_5 : CertificateAt 3 24 5 := by decide +kernel
theorem row_3_24 : ThresholdAt 3 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 24 0 cell_3_24_0
    | exact certificate_sound 3 24 1 cell_3_24_1
    | exact certificate_sound 3 24 2 cell_3_24_2
    | exact certificate_sound 3 24 3 cell_3_24_3
    | exact certificate_sound 3 24 4 cell_3_24_4
    | exact certificate_sound 3 24 5 cell_3_24_5
theorem cell_3_25_0 : CertificateAt 3 25 0 := by decide +kernel
theorem cell_3_25_1 : CertificateAt 3 25 1 := by decide +kernel
theorem cell_3_25_2 : CertificateAt 3 25 2 := by decide +kernel
theorem cell_3_25_3 : CertificateAt 3 25 3 := by decide +kernel
theorem cell_3_25_4 : CertificateAt 3 25 4 := by decide +kernel
theorem cell_3_25_5 : CertificateAt 3 25 5 := by decide +kernel
theorem row_3_25 : ThresholdAt 3 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 25 0 cell_3_25_0
    | exact certificate_sound 3 25 1 cell_3_25_1
    | exact certificate_sound 3 25 2 cell_3_25_2
    | exact certificate_sound 3 25 3 cell_3_25_3
    | exact certificate_sound 3 25 4 cell_3_25_4
    | exact certificate_sound 3 25 5 cell_3_25_5
theorem cell_3_26_0 : CertificateAt 3 26 0 := by decide +kernel
theorem cell_3_26_1 : CertificateAt 3 26 1 := by decide +kernel
theorem cell_3_26_2 : CertificateAt 3 26 2 := by decide +kernel
theorem cell_3_26_3 : CertificateAt 3 26 3 := by decide +kernel
theorem cell_3_26_4 : CertificateAt 3 26 4 := by decide +kernel
theorem cell_3_26_5 : CertificateAt 3 26 5 := by decide +kernel
theorem row_3_26 : ThresholdAt 3 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 26 0 cell_3_26_0
    | exact certificate_sound 3 26 1 cell_3_26_1
    | exact certificate_sound 3 26 2 cell_3_26_2
    | exact certificate_sound 3 26 3 cell_3_26_3
    | exact certificate_sound 3 26 4 cell_3_26_4
    | exact certificate_sound 3 26 5 cell_3_26_5
theorem cell_3_27_0 : CertificateAt 3 27 0 := by decide +kernel
theorem cell_3_27_1 : CertificateAt 3 27 1 := by decide +kernel
theorem cell_3_27_2 : CertificateAt 3 27 2 := by decide +kernel
theorem cell_3_27_3 : CertificateAt 3 27 3 := by decide +kernel
theorem cell_3_27_4 : CertificateAt 3 27 4 := by decide +kernel
theorem cell_3_27_5 : CertificateAt 3 27 5 := by decide +kernel
theorem row_3_27 : ThresholdAt 3 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 27 0 cell_3_27_0
    | exact certificate_sound 3 27 1 cell_3_27_1
    | exact certificate_sound 3 27 2 cell_3_27_2
    | exact certificate_sound 3 27 3 cell_3_27_3
    | exact certificate_sound 3 27 4 cell_3_27_4
    | exact certificate_sound 3 27 5 cell_3_27_5
theorem cell_3_28_0 : CertificateAt 3 28 0 := by decide +kernel
theorem cell_3_28_1 : CertificateAt 3 28 1 := by decide +kernel
theorem cell_3_28_2 : CertificateAt 3 28 2 := by decide +kernel
theorem cell_3_28_3 : CertificateAt 3 28 3 := by decide +kernel
theorem cell_3_28_4 : CertificateAt 3 28 4 := by decide +kernel
theorem cell_3_28_5 : CertificateAt 3 28 5 := by decide +kernel
theorem row_3_28 : ThresholdAt 3 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 28 0 cell_3_28_0
    | exact certificate_sound 3 28 1 cell_3_28_1
    | exact certificate_sound 3 28 2 cell_3_28_2
    | exact certificate_sound 3 28 3 cell_3_28_3
    | exact certificate_sound 3 28 4 cell_3_28_4
    | exact certificate_sound 3 28 5 cell_3_28_5
theorem cell_3_29_0 : CertificateAt 3 29 0 := by decide +kernel
theorem cell_3_29_1 : CertificateAt 3 29 1 := by decide +kernel
theorem cell_3_29_2 : CertificateAt 3 29 2 := by decide +kernel
theorem cell_3_29_3 : CertificateAt 3 29 3 := by decide +kernel
theorem cell_3_29_4 : CertificateAt 3 29 4 := by decide +kernel
theorem cell_3_29_5 : CertificateAt 3 29 5 := by decide +kernel
theorem row_3_29 : ThresholdAt 3 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 29 0 cell_3_29_0
    | exact certificate_sound 3 29 1 cell_3_29_1
    | exact certificate_sound 3 29 2 cell_3_29_2
    | exact certificate_sound 3 29 3 cell_3_29_3
    | exact certificate_sound 3 29 4 cell_3_29_4
    | exact certificate_sound 3 29 5 cell_3_29_5
theorem cell_3_30_0 : CertificateAt 3 30 0 := by decide +kernel
theorem cell_3_30_1 : CertificateAt 3 30 1 := by decide +kernel
theorem cell_3_30_2 : CertificateAt 3 30 2 := by decide +kernel
theorem cell_3_30_3 : CertificateAt 3 30 3 := by decide +kernel
theorem cell_3_30_4 : CertificateAt 3 30 4 := by decide +kernel
theorem cell_3_30_5 : CertificateAt 3 30 5 := by decide +kernel
theorem row_3_30 : ThresholdAt 3 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 30 0 cell_3_30_0
    | exact certificate_sound 3 30 1 cell_3_30_1
    | exact certificate_sound 3 30 2 cell_3_30_2
    | exact certificate_sound 3 30 3 cell_3_30_3
    | exact certificate_sound 3 30 4 cell_3_30_4
    | exact certificate_sound 3 30 5 cell_3_30_5
theorem cell_3_31_0 : CertificateAt 3 31 0 := by decide +kernel
theorem cell_3_31_1 : CertificateAt 3 31 1 := by decide +kernel
theorem cell_3_31_2 : CertificateAt 3 31 2 := by decide +kernel
theorem cell_3_31_3 : CertificateAt 3 31 3 := by decide +kernel
theorem cell_3_31_4 : CertificateAt 3 31 4 := by decide +kernel
theorem cell_3_31_5 : CertificateAt 3 31 5 := by decide +kernel
theorem row_3_31 : ThresholdAt 3 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 31 0 cell_3_31_0
    | exact certificate_sound 3 31 1 cell_3_31_1
    | exact certificate_sound 3 31 2 cell_3_31_2
    | exact certificate_sound 3 31 3 cell_3_31_3
    | exact certificate_sound 3 31 4 cell_3_31_4
    | exact certificate_sound 3 31 5 cell_3_31_5
theorem cell_3_32_0 : CertificateAt 3 32 0 := by decide +kernel
theorem cell_3_32_1 : CertificateAt 3 32 1 := by decide +kernel
theorem cell_3_32_2 : CertificateAt 3 32 2 := by decide +kernel
theorem cell_3_32_3 : CertificateAt 3 32 3 := by decide +kernel
theorem cell_3_32_4 : CertificateAt 3 32 4 := by decide +kernel
theorem cell_3_32_5 : CertificateAt 3 32 5 := by decide +kernel
theorem row_3_32 : ThresholdAt 3 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 32 0 cell_3_32_0
    | exact certificate_sound 3 32 1 cell_3_32_1
    | exact certificate_sound 3 32 2 cell_3_32_2
    | exact certificate_sound 3 32 3 cell_3_32_3
    | exact certificate_sound 3 32 4 cell_3_32_4
    | exact certificate_sound 3 32 5 cell_3_32_5
theorem cell_3_33_0 : CertificateAt 3 33 0 := by decide +kernel
theorem cell_3_33_1 : CertificateAt 3 33 1 := by decide +kernel
theorem cell_3_33_2 : CertificateAt 3 33 2 := by decide +kernel
theorem cell_3_33_3 : CertificateAt 3 33 3 := by decide +kernel
theorem cell_3_33_4 : CertificateAt 3 33 4 := by decide +kernel
theorem cell_3_33_5 : CertificateAt 3 33 5 := by decide +kernel
theorem row_3_33 : ThresholdAt 3 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 33 0 cell_3_33_0
    | exact certificate_sound 3 33 1 cell_3_33_1
    | exact certificate_sound 3 33 2 cell_3_33_2
    | exact certificate_sound 3 33 3 cell_3_33_3
    | exact certificate_sound 3 33 4 cell_3_33_4
    | exact certificate_sound 3 33 5 cell_3_33_5
theorem cell_3_34_0 : CertificateAt 3 34 0 := by decide +kernel
theorem cell_3_34_1 : CertificateAt 3 34 1 := by decide +kernel
theorem cell_3_34_2 : CertificateAt 3 34 2 := by decide +kernel
theorem cell_3_34_3 : CertificateAt 3 34 3 := by decide +kernel
theorem cell_3_34_4 : CertificateAt 3 34 4 := by decide +kernel
theorem cell_3_34_5 : CertificateAt 3 34 5 := by decide +kernel
theorem row_3_34 : ThresholdAt 3 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 34 0 cell_3_34_0
    | exact certificate_sound 3 34 1 cell_3_34_1
    | exact certificate_sound 3 34 2 cell_3_34_2
    | exact certificate_sound 3 34 3 cell_3_34_3
    | exact certificate_sound 3 34 4 cell_3_34_4
    | exact certificate_sound 3 34 5 cell_3_34_5
theorem cell_3_35_0 : CertificateAt 3 35 0 := by decide +kernel
theorem cell_3_35_1 : CertificateAt 3 35 1 := by decide +kernel
theorem cell_3_35_2 : CertificateAt 3 35 2 := by decide +kernel
theorem cell_3_35_3 : CertificateAt 3 35 3 := by decide +kernel
theorem cell_3_35_4 : CertificateAt 3 35 4 := by decide +kernel
theorem cell_3_35_5 : CertificateAt 3 35 5 := by decide +kernel
theorem row_3_35 : ThresholdAt 3 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 35 0 cell_3_35_0
    | exact certificate_sound 3 35 1 cell_3_35_1
    | exact certificate_sound 3 35 2 cell_3_35_2
    | exact certificate_sound 3 35 3 cell_3_35_3
    | exact certificate_sound 3 35 4 cell_3_35_4
    | exact certificate_sound 3 35 5 cell_3_35_5
theorem cell_3_36_0 : CertificateAt 3 36 0 := by decide +kernel
theorem cell_3_36_1 : CertificateAt 3 36 1 := by decide +kernel
theorem cell_3_36_2 : CertificateAt 3 36 2 := by decide +kernel
theorem cell_3_36_3 : CertificateAt 3 36 3 := by decide +kernel
theorem cell_3_36_4 : CertificateAt 3 36 4 := by decide +kernel
theorem cell_3_36_5 : CertificateAt 3 36 5 := by decide +kernel
theorem row_3_36 : ThresholdAt 3 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 36 0 cell_3_36_0
    | exact certificate_sound 3 36 1 cell_3_36_1
    | exact certificate_sound 3 36 2 cell_3_36_2
    | exact certificate_sound 3 36 3 cell_3_36_3
    | exact certificate_sound 3 36 4 cell_3_36_4
    | exact certificate_sound 3 36 5 cell_3_36_5
theorem cell_3_37_0 : CertificateAt 3 37 0 := by decide +kernel
theorem cell_3_37_1 : CertificateAt 3 37 1 := by decide +kernel
theorem cell_3_37_2 : CertificateAt 3 37 2 := by decide +kernel
theorem cell_3_37_3 : CertificateAt 3 37 3 := by decide +kernel
theorem cell_3_37_4 : CertificateAt 3 37 4 := by decide +kernel
theorem cell_3_37_5 : CertificateAt 3 37 5 := by decide +kernel
theorem row_3_37 : ThresholdAt 3 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 37 0 cell_3_37_0
    | exact certificate_sound 3 37 1 cell_3_37_1
    | exact certificate_sound 3 37 2 cell_3_37_2
    | exact certificate_sound 3 37 3 cell_3_37_3
    | exact certificate_sound 3 37 4 cell_3_37_4
    | exact certificate_sound 3 37 5 cell_3_37_5
theorem cell_3_38_0 : CertificateAt 3 38 0 := by decide +kernel
theorem cell_3_38_1 : CertificateAt 3 38 1 := by decide +kernel
theorem cell_3_38_2 : CertificateAt 3 38 2 := by decide +kernel
theorem cell_3_38_3 : CertificateAt 3 38 3 := by decide +kernel
theorem cell_3_38_4 : CertificateAt 3 38 4 := by decide +kernel
theorem cell_3_38_5 : CertificateAt 3 38 5 := by decide +kernel
theorem row_3_38 : ThresholdAt 3 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 38 0 cell_3_38_0
    | exact certificate_sound 3 38 1 cell_3_38_1
    | exact certificate_sound 3 38 2 cell_3_38_2
    | exact certificate_sound 3 38 3 cell_3_38_3
    | exact certificate_sound 3 38 4 cell_3_38_4
    | exact certificate_sound 3 38 5 cell_3_38_5
theorem cell_3_39_0 : CertificateAt 3 39 0 := by decide +kernel
theorem cell_3_39_1 : CertificateAt 3 39 1 := by decide +kernel
theorem cell_3_39_2 : CertificateAt 3 39 2 := by decide +kernel
theorem cell_3_39_3 : CertificateAt 3 39 3 := by decide +kernel
theorem cell_3_39_4 : CertificateAt 3 39 4 := by decide +kernel
theorem cell_3_39_5 : CertificateAt 3 39 5 := by decide +kernel
theorem row_3_39 : ThresholdAt 3 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 39 0 cell_3_39_0
    | exact certificate_sound 3 39 1 cell_3_39_1
    | exact certificate_sound 3 39 2 cell_3_39_2
    | exact certificate_sound 3 39 3 cell_3_39_3
    | exact certificate_sound 3 39 4 cell_3_39_4
    | exact certificate_sound 3 39 5 cell_3_39_5
theorem cell_3_40_0 : CertificateAt 3 40 0 := by decide +kernel
theorem cell_3_40_1 : CertificateAt 3 40 1 := by decide +kernel
theorem cell_3_40_2 : CertificateAt 3 40 2 := by decide +kernel
theorem cell_3_40_3 : CertificateAt 3 40 3 := by decide +kernel
theorem cell_3_40_4 : CertificateAt 3 40 4 := by decide +kernel
theorem cell_3_40_5 : CertificateAt 3 40 5 := by decide +kernel
theorem row_3_40 : ThresholdAt 3 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 40 0 cell_3_40_0
    | exact certificate_sound 3 40 1 cell_3_40_1
    | exact certificate_sound 3 40 2 cell_3_40_2
    | exact certificate_sound 3 40 3 cell_3_40_3
    | exact certificate_sound 3 40 4 cell_3_40_4
    | exact certificate_sound 3 40 5 cell_3_40_5
theorem cell_3_41_0 : CertificateAt 3 41 0 := by decide +kernel
theorem cell_3_41_1 : CertificateAt 3 41 1 := by decide +kernel
theorem cell_3_41_2 : CertificateAt 3 41 2 := by decide +kernel
theorem cell_3_41_3 : CertificateAt 3 41 3 := by decide +kernel
theorem cell_3_41_4 : CertificateAt 3 41 4 := by decide +kernel
theorem cell_3_41_5 : CertificateAt 3 41 5 := by decide +kernel
theorem row_3_41 : ThresholdAt 3 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 41 0 cell_3_41_0
    | exact certificate_sound 3 41 1 cell_3_41_1
    | exact certificate_sound 3 41 2 cell_3_41_2
    | exact certificate_sound 3 41 3 cell_3_41_3
    | exact certificate_sound 3 41 4 cell_3_41_4
    | exact certificate_sound 3 41 5 cell_3_41_5
theorem cell_3_42_0 : CertificateAt 3 42 0 := by decide +kernel
theorem cell_3_42_1 : CertificateAt 3 42 1 := by decide +kernel
theorem cell_3_42_2 : CertificateAt 3 42 2 := by decide +kernel
theorem cell_3_42_3 : CertificateAt 3 42 3 := by decide +kernel
theorem cell_3_42_4 : CertificateAt 3 42 4 := by decide +kernel
theorem cell_3_42_5 : CertificateAt 3 42 5 := by decide +kernel
theorem row_3_42 : ThresholdAt 3 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 42 0 cell_3_42_0
    | exact certificate_sound 3 42 1 cell_3_42_1
    | exact certificate_sound 3 42 2 cell_3_42_2
    | exact certificate_sound 3 42 3 cell_3_42_3
    | exact certificate_sound 3 42 4 cell_3_42_4
    | exact certificate_sound 3 42 5 cell_3_42_5
theorem cell_3_43_0 : CertificateAt 3 43 0 := by decide +kernel
theorem cell_3_43_1 : CertificateAt 3 43 1 := by decide +kernel
theorem cell_3_43_2 : CertificateAt 3 43 2 := by decide +kernel
theorem cell_3_43_3 : CertificateAt 3 43 3 := by decide +kernel
theorem cell_3_43_4 : CertificateAt 3 43 4 := by decide +kernel
theorem cell_3_43_5 : CertificateAt 3 43 5 := by decide +kernel
theorem row_3_43 : ThresholdAt 3 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 43 0 cell_3_43_0
    | exact certificate_sound 3 43 1 cell_3_43_1
    | exact certificate_sound 3 43 2 cell_3_43_2
    | exact certificate_sound 3 43 3 cell_3_43_3
    | exact certificate_sound 3 43 4 cell_3_43_4
    | exact certificate_sound 3 43 5 cell_3_43_5
theorem cell_3_44_0 : CertificateAt 3 44 0 := by decide +kernel
theorem cell_3_44_1 : CertificateAt 3 44 1 := by decide +kernel
theorem cell_3_44_2 : CertificateAt 3 44 2 := by decide +kernel
theorem cell_3_44_3 : CertificateAt 3 44 3 := by decide +kernel
theorem cell_3_44_4 : CertificateAt 3 44 4 := by decide +kernel
theorem cell_3_44_5 : CertificateAt 3 44 5 := by decide +kernel
theorem row_3_44 : ThresholdAt 3 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 44 0 cell_3_44_0
    | exact certificate_sound 3 44 1 cell_3_44_1
    | exact certificate_sound 3 44 2 cell_3_44_2
    | exact certificate_sound 3 44 3 cell_3_44_3
    | exact certificate_sound 3 44 4 cell_3_44_4
    | exact certificate_sound 3 44 5 cell_3_44_5
theorem cell_3_45_0 : CertificateAt 3 45 0 := by decide +kernel
theorem cell_3_45_1 : CertificateAt 3 45 1 := by decide +kernel
theorem cell_3_45_2 : CertificateAt 3 45 2 := by decide +kernel
theorem cell_3_45_3 : CertificateAt 3 45 3 := by decide +kernel
theorem cell_3_45_4 : CertificateAt 3 45 4 := by decide +kernel
theorem cell_3_45_5 : CertificateAt 3 45 5 := by decide +kernel
theorem row_3_45 : ThresholdAt 3 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 45 0 cell_3_45_0
    | exact certificate_sound 3 45 1 cell_3_45_1
    | exact certificate_sound 3 45 2 cell_3_45_2
    | exact certificate_sound 3 45 3 cell_3_45_3
    | exact certificate_sound 3 45 4 cell_3_45_4
    | exact certificate_sound 3 45 5 cell_3_45_5
theorem cell_3_46_0 : CertificateAt 3 46 0 := by decide +kernel
theorem cell_3_46_1 : CertificateAt 3 46 1 := by decide +kernel
theorem cell_3_46_2 : CertificateAt 3 46 2 := by decide +kernel
theorem cell_3_46_3 : CertificateAt 3 46 3 := by decide +kernel
theorem cell_3_46_4 : CertificateAt 3 46 4 := by decide +kernel
theorem cell_3_46_5 : CertificateAt 3 46 5 := by decide +kernel
theorem row_3_46 : ThresholdAt 3 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 46 0 cell_3_46_0
    | exact certificate_sound 3 46 1 cell_3_46_1
    | exact certificate_sound 3 46 2 cell_3_46_2
    | exact certificate_sound 3 46 3 cell_3_46_3
    | exact certificate_sound 3 46 4 cell_3_46_4
    | exact certificate_sound 3 46 5 cell_3_46_5
theorem cell_3_47_0 : CertificateAt 3 47 0 := by decide +kernel
theorem cell_3_47_1 : CertificateAt 3 47 1 := by decide +kernel
theorem cell_3_47_2 : CertificateAt 3 47 2 := by decide +kernel
theorem cell_3_47_3 : CertificateAt 3 47 3 := by decide +kernel
theorem cell_3_47_4 : CertificateAt 3 47 4 := by decide +kernel
theorem cell_3_47_5 : CertificateAt 3 47 5 := by decide +kernel
theorem row_3_47 : ThresholdAt 3 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 47 0 cell_3_47_0
    | exact certificate_sound 3 47 1 cell_3_47_1
    | exact certificate_sound 3 47 2 cell_3_47_2
    | exact certificate_sound 3 47 3 cell_3_47_3
    | exact certificate_sound 3 47 4 cell_3_47_4
    | exact certificate_sound 3 47 5 cell_3_47_5
theorem cell_3_48_0 : CertificateAt 3 48 0 := by decide +kernel
theorem cell_3_48_1 : CertificateAt 3 48 1 := by decide +kernel
theorem cell_3_48_2 : CertificateAt 3 48 2 := by decide +kernel
theorem cell_3_48_3 : CertificateAt 3 48 3 := by decide +kernel
theorem cell_3_48_4 : CertificateAt 3 48 4 := by decide +kernel
theorem cell_3_48_5 : CertificateAt 3 48 5 := by decide +kernel
theorem row_3_48 : ThresholdAt 3 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 48 0 cell_3_48_0
    | exact certificate_sound 3 48 1 cell_3_48_1
    | exact certificate_sound 3 48 2 cell_3_48_2
    | exact certificate_sound 3 48 3 cell_3_48_3
    | exact certificate_sound 3 48 4 cell_3_48_4
    | exact certificate_sound 3 48 5 cell_3_48_5
theorem cell_3_49_0 : CertificateAt 3 49 0 := by decide +kernel
theorem cell_3_49_1 : CertificateAt 3 49 1 := by decide +kernel
theorem cell_3_49_2 : CertificateAt 3 49 2 := by decide +kernel
theorem cell_3_49_3 : CertificateAt 3 49 3 := by decide +kernel
theorem cell_3_49_4 : CertificateAt 3 49 4 := by decide +kernel
theorem cell_3_49_5 : CertificateAt 3 49 5 := by decide +kernel
theorem row_3_49 : ThresholdAt 3 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 49 0 cell_3_49_0
    | exact certificate_sound 3 49 1 cell_3_49_1
    | exact certificate_sound 3 49 2 cell_3_49_2
    | exact certificate_sound 3 49 3 cell_3_49_3
    | exact certificate_sound 3 49 4 cell_3_49_4
    | exact certificate_sound 3 49 5 cell_3_49_5
theorem cell_3_50_0 : CertificateAt 3 50 0 := by decide +kernel
theorem cell_3_50_1 : CertificateAt 3 50 1 := by decide +kernel
theorem cell_3_50_2 : CertificateAt 3 50 2 := by decide +kernel
theorem cell_3_50_3 : CertificateAt 3 50 3 := by decide +kernel
theorem cell_3_50_4 : CertificateAt 3 50 4 := by decide +kernel
theorem cell_3_50_5 : CertificateAt 3 50 5 := by decide +kernel
theorem row_3_50 : ThresholdAt 3 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 50 0 cell_3_50_0
    | exact certificate_sound 3 50 1 cell_3_50_1
    | exact certificate_sound 3 50 2 cell_3_50_2
    | exact certificate_sound 3 50 3 cell_3_50_3
    | exact certificate_sound 3 50 4 cell_3_50_4
    | exact certificate_sound 3 50 5 cell_3_50_5
theorem cell_3_51_0 : CertificateAt 3 51 0 := by decide +kernel
theorem cell_3_51_1 : CertificateAt 3 51 1 := by decide +kernel
theorem cell_3_51_2 : CertificateAt 3 51 2 := by decide +kernel
theorem cell_3_51_3 : CertificateAt 3 51 3 := by decide +kernel
theorem cell_3_51_4 : CertificateAt 3 51 4 := by decide +kernel
theorem cell_3_51_5 : CertificateAt 3 51 5 := by decide +kernel
theorem row_3_51 : ThresholdAt 3 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 51 0 cell_3_51_0
    | exact certificate_sound 3 51 1 cell_3_51_1
    | exact certificate_sound 3 51 2 cell_3_51_2
    | exact certificate_sound 3 51 3 cell_3_51_3
    | exact certificate_sound 3 51 4 cell_3_51_4
    | exact certificate_sound 3 51 5 cell_3_51_5
theorem cell_3_52_0 : CertificateAt 3 52 0 := by decide +kernel
theorem cell_3_52_1 : CertificateAt 3 52 1 := by decide +kernel
theorem cell_3_52_2 : CertificateAt 3 52 2 := by decide +kernel
theorem cell_3_52_3 : CertificateAt 3 52 3 := by decide +kernel
theorem cell_3_52_4 : CertificateAt 3 52 4 := by decide +kernel
theorem cell_3_52_5 : CertificateAt 3 52 5 := by decide +kernel
theorem row_3_52 : ThresholdAt 3 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 52 0 cell_3_52_0
    | exact certificate_sound 3 52 1 cell_3_52_1
    | exact certificate_sound 3 52 2 cell_3_52_2
    | exact certificate_sound 3 52 3 cell_3_52_3
    | exact certificate_sound 3 52 4 cell_3_52_4
    | exact certificate_sound 3 52 5 cell_3_52_5
theorem cell_3_53_0 : CertificateAt 3 53 0 := by decide +kernel
theorem cell_3_53_1 : CertificateAt 3 53 1 := by decide +kernel
theorem cell_3_53_2 : CertificateAt 3 53 2 := by decide +kernel
theorem cell_3_53_3 : CertificateAt 3 53 3 := by decide +kernel
theorem cell_3_53_4 : CertificateAt 3 53 4 := by decide +kernel
theorem cell_3_53_5 : CertificateAt 3 53 5 := by decide +kernel
theorem row_3_53 : ThresholdAt 3 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 53 0 cell_3_53_0
    | exact certificate_sound 3 53 1 cell_3_53_1
    | exact certificate_sound 3 53 2 cell_3_53_2
    | exact certificate_sound 3 53 3 cell_3_53_3
    | exact certificate_sound 3 53 4 cell_3_53_4
    | exact certificate_sound 3 53 5 cell_3_53_5
theorem cell_3_54_0 : CertificateAt 3 54 0 := by decide +kernel
theorem cell_3_54_1 : CertificateAt 3 54 1 := by decide +kernel
theorem cell_3_54_2 : CertificateAt 3 54 2 := by decide +kernel
theorem cell_3_54_3 : CertificateAt 3 54 3 := by decide +kernel
theorem cell_3_54_4 : CertificateAt 3 54 4 := by decide +kernel
theorem cell_3_54_5 : CertificateAt 3 54 5 := by decide +kernel
theorem row_3_54 : ThresholdAt 3 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 54 0 cell_3_54_0
    | exact certificate_sound 3 54 1 cell_3_54_1
    | exact certificate_sound 3 54 2 cell_3_54_2
    | exact certificate_sound 3 54 3 cell_3_54_3
    | exact certificate_sound 3 54 4 cell_3_54_4
    | exact certificate_sound 3 54 5 cell_3_54_5
theorem cell_3_55_0 : CertificateAt 3 55 0 := by decide +kernel
theorem cell_3_55_1 : CertificateAt 3 55 1 := by decide +kernel
theorem cell_3_55_2 : CertificateAt 3 55 2 := by decide +kernel
theorem cell_3_55_3 : CertificateAt 3 55 3 := by decide +kernel
theorem cell_3_55_4 : CertificateAt 3 55 4 := by decide +kernel
theorem cell_3_55_5 : CertificateAt 3 55 5 := by decide +kernel
theorem row_3_55 : ThresholdAt 3 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 55 0 cell_3_55_0
    | exact certificate_sound 3 55 1 cell_3_55_1
    | exact certificate_sound 3 55 2 cell_3_55_2
    | exact certificate_sound 3 55 3 cell_3_55_3
    | exact certificate_sound 3 55 4 cell_3_55_4
    | exact certificate_sound 3 55 5 cell_3_55_5
theorem cell_3_56_0 : CertificateAt 3 56 0 := by decide +kernel
theorem cell_3_56_1 : CertificateAt 3 56 1 := by decide +kernel
theorem cell_3_56_2 : CertificateAt 3 56 2 := by decide +kernel
theorem cell_3_56_3 : CertificateAt 3 56 3 := by decide +kernel
theorem cell_3_56_4 : CertificateAt 3 56 4 := by decide +kernel
theorem cell_3_56_5 : CertificateAt 3 56 5 := by decide +kernel
theorem row_3_56 : ThresholdAt 3 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 56 0 cell_3_56_0
    | exact certificate_sound 3 56 1 cell_3_56_1
    | exact certificate_sound 3 56 2 cell_3_56_2
    | exact certificate_sound 3 56 3 cell_3_56_3
    | exact certificate_sound 3 56 4 cell_3_56_4
    | exact certificate_sound 3 56 5 cell_3_56_5
theorem cell_3_57_0 : CertificateAt 3 57 0 := by decide +kernel
theorem cell_3_57_1 : CertificateAt 3 57 1 := by decide +kernel
theorem cell_3_57_2 : CertificateAt 3 57 2 := by decide +kernel
theorem cell_3_57_3 : CertificateAt 3 57 3 := by decide +kernel
theorem cell_3_57_4 : CertificateAt 3 57 4 := by decide +kernel
theorem cell_3_57_5 : CertificateAt 3 57 5 := by decide +kernel
theorem row_3_57 : ThresholdAt 3 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 57 0 cell_3_57_0
    | exact certificate_sound 3 57 1 cell_3_57_1
    | exact certificate_sound 3 57 2 cell_3_57_2
    | exact certificate_sound 3 57 3 cell_3_57_3
    | exact certificate_sound 3 57 4 cell_3_57_4
    | exact certificate_sound 3 57 5 cell_3_57_5
theorem cell_3_58_0 : CertificateAt 3 58 0 := by decide +kernel
theorem cell_3_58_1 : CertificateAt 3 58 1 := by decide +kernel
theorem cell_3_58_2 : CertificateAt 3 58 2 := by decide +kernel
theorem cell_3_58_3 : CertificateAt 3 58 3 := by decide +kernel
theorem cell_3_58_4 : CertificateAt 3 58 4 := by decide +kernel
theorem cell_3_58_5 : CertificateAt 3 58 5 := by decide +kernel
theorem row_3_58 : ThresholdAt 3 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 58 0 cell_3_58_0
    | exact certificate_sound 3 58 1 cell_3_58_1
    | exact certificate_sound 3 58 2 cell_3_58_2
    | exact certificate_sound 3 58 3 cell_3_58_3
    | exact certificate_sound 3 58 4 cell_3_58_4
    | exact certificate_sound 3 58 5 cell_3_58_5
theorem cell_3_59_0 : CertificateAt 3 59 0 := by decide +kernel
theorem cell_3_59_1 : CertificateAt 3 59 1 := by decide +kernel
theorem cell_3_59_2 : CertificateAt 3 59 2 := by decide +kernel
theorem cell_3_59_3 : CertificateAt 3 59 3 := by decide +kernel
theorem cell_3_59_4 : CertificateAt 3 59 4 := by decide +kernel
theorem cell_3_59_5 : CertificateAt 3 59 5 := by decide +kernel
theorem row_3_59 : ThresholdAt 3 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 59 0 cell_3_59_0
    | exact certificate_sound 3 59 1 cell_3_59_1
    | exact certificate_sound 3 59 2 cell_3_59_2
    | exact certificate_sound 3 59 3 cell_3_59_3
    | exact certificate_sound 3 59 4 cell_3_59_4
    | exact certificate_sound 3 59 5 cell_3_59_5
theorem cell_3_60_0 : CertificateAt 3 60 0 := by decide +kernel
theorem cell_3_60_1 : CertificateAt 3 60 1 := by decide +kernel
theorem cell_3_60_2 : CertificateAt 3 60 2 := by decide +kernel
theorem cell_3_60_3 : CertificateAt 3 60 3 := by decide +kernel
theorem cell_3_60_4 : CertificateAt 3 60 4 := by decide +kernel
theorem cell_3_60_5 : CertificateAt 3 60 5 := by decide +kernel
theorem row_3_60 : ThresholdAt 3 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 60 0 cell_3_60_0
    | exact certificate_sound 3 60 1 cell_3_60_1
    | exact certificate_sound 3 60 2 cell_3_60_2
    | exact certificate_sound 3 60 3 cell_3_60_3
    | exact certificate_sound 3 60 4 cell_3_60_4
    | exact certificate_sound 3 60 5 cell_3_60_5
theorem cell_3_61_0 : CertificateAt 3 61 0 := by decide +kernel
theorem cell_3_61_1 : CertificateAt 3 61 1 := by decide +kernel
theorem cell_3_61_2 : CertificateAt 3 61 2 := by decide +kernel
theorem cell_3_61_3 : CertificateAt 3 61 3 := by decide +kernel
theorem cell_3_61_4 : CertificateAt 3 61 4 := by decide +kernel
theorem cell_3_61_5 : CertificateAt 3 61 5 := by decide +kernel
theorem row_3_61 : ThresholdAt 3 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 61 0 cell_3_61_0
    | exact certificate_sound 3 61 1 cell_3_61_1
    | exact certificate_sound 3 61 2 cell_3_61_2
    | exact certificate_sound 3 61 3 cell_3_61_3
    | exact certificate_sound 3 61 4 cell_3_61_4
    | exact certificate_sound 3 61 5 cell_3_61_5
theorem cell_3_62_0 : CertificateAt 3 62 0 := by decide +kernel
theorem cell_3_62_1 : CertificateAt 3 62 1 := by decide +kernel
theorem cell_3_62_2 : CertificateAt 3 62 2 := by decide +kernel
theorem cell_3_62_3 : CertificateAt 3 62 3 := by decide +kernel
theorem cell_3_62_4 : CertificateAt 3 62 4 := by decide +kernel
theorem cell_3_62_5 : CertificateAt 3 62 5 := by decide +kernel
theorem row_3_62 : ThresholdAt 3 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 62 0 cell_3_62_0
    | exact certificate_sound 3 62 1 cell_3_62_1
    | exact certificate_sound 3 62 2 cell_3_62_2
    | exact certificate_sound 3 62 3 cell_3_62_3
    | exact certificate_sound 3 62 4 cell_3_62_4
    | exact certificate_sound 3 62 5 cell_3_62_5
theorem cell_3_63_0 : CertificateAt 3 63 0 := by decide +kernel
theorem cell_3_63_1 : CertificateAt 3 63 1 := by decide +kernel
theorem cell_3_63_2 : CertificateAt 3 63 2 := by decide +kernel
theorem cell_3_63_3 : CertificateAt 3 63 3 := by decide +kernel
theorem cell_3_63_4 : CertificateAt 3 63 4 := by decide +kernel
theorem cell_3_63_5 : CertificateAt 3 63 5 := by decide +kernel
theorem row_3_63 : ThresholdAt 3 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 63 0 cell_3_63_0
    | exact certificate_sound 3 63 1 cell_3_63_1
    | exact certificate_sound 3 63 2 cell_3_63_2
    | exact certificate_sound 3 63 3 cell_3_63_3
    | exact certificate_sound 3 63 4 cell_3_63_4
    | exact certificate_sound 3 63 5 cell_3_63_5
theorem cell_3_64_0 : CertificateAt 3 64 0 := by decide +kernel
theorem cell_3_64_1 : CertificateAt 3 64 1 := by decide +kernel
theorem cell_3_64_2 : CertificateAt 3 64 2 := by decide +kernel
theorem cell_3_64_3 : CertificateAt 3 64 3 := by decide +kernel
theorem cell_3_64_4 : CertificateAt 3 64 4 := by decide +kernel
theorem cell_3_64_5 : CertificateAt 3 64 5 := by decide +kernel
theorem row_3_64 : ThresholdAt 3 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 64 0 cell_3_64_0
    | exact certificate_sound 3 64 1 cell_3_64_1
    | exact certificate_sound 3 64 2 cell_3_64_2
    | exact certificate_sound 3 64 3 cell_3_64_3
    | exact certificate_sound 3 64 4 cell_3_64_4
    | exact certificate_sound 3 64 5 cell_3_64_5
theorem cell_3_65_0 : CertificateAt 3 65 0 := by decide +kernel
theorem cell_3_65_1 : CertificateAt 3 65 1 := by decide +kernel
theorem cell_3_65_2 : CertificateAt 3 65 2 := by decide +kernel
theorem cell_3_65_3 : CertificateAt 3 65 3 := by decide +kernel
theorem cell_3_65_4 : CertificateAt 3 65 4 := by decide +kernel
theorem cell_3_65_5 : CertificateAt 3 65 5 := by decide +kernel
theorem row_3_65 : ThresholdAt 3 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 65 0 cell_3_65_0
    | exact certificate_sound 3 65 1 cell_3_65_1
    | exact certificate_sound 3 65 2 cell_3_65_2
    | exact certificate_sound 3 65 3 cell_3_65_3
    | exact certificate_sound 3 65 4 cell_3_65_4
    | exact certificate_sound 3 65 5 cell_3_65_5
theorem cell_3_66_0 : CertificateAt 3 66 0 := by decide +kernel
theorem cell_3_66_1 : CertificateAt 3 66 1 := by decide +kernel
theorem cell_3_66_2 : CertificateAt 3 66 2 := by decide +kernel
theorem cell_3_66_3 : CertificateAt 3 66 3 := by decide +kernel
theorem cell_3_66_4 : CertificateAt 3 66 4 := by decide +kernel
theorem cell_3_66_5 : CertificateAt 3 66 5 := by decide +kernel
theorem row_3_66 : ThresholdAt 3 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 66 0 cell_3_66_0
    | exact certificate_sound 3 66 1 cell_3_66_1
    | exact certificate_sound 3 66 2 cell_3_66_2
    | exact certificate_sound 3 66 3 cell_3_66_3
    | exact certificate_sound 3 66 4 cell_3_66_4
    | exact certificate_sound 3 66 5 cell_3_66_5
theorem cell_3_67_0 : CertificateAt 3 67 0 := by decide +kernel
theorem cell_3_67_1 : CertificateAt 3 67 1 := by decide +kernel
theorem cell_3_67_2 : CertificateAt 3 67 2 := by decide +kernel
theorem cell_3_67_3 : CertificateAt 3 67 3 := by decide +kernel
theorem cell_3_67_4 : CertificateAt 3 67 4 := by decide +kernel
theorem cell_3_67_5 : CertificateAt 3 67 5 := by decide +kernel
theorem row_3_67 : ThresholdAt 3 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 67 0 cell_3_67_0
    | exact certificate_sound 3 67 1 cell_3_67_1
    | exact certificate_sound 3 67 2 cell_3_67_2
    | exact certificate_sound 3 67 3 cell_3_67_3
    | exact certificate_sound 3 67 4 cell_3_67_4
    | exact certificate_sound 3 67 5 cell_3_67_5
theorem cell_3_68_0 : CertificateAt 3 68 0 := by decide +kernel
theorem cell_3_68_1 : CertificateAt 3 68 1 := by decide +kernel
theorem cell_3_68_2 : CertificateAt 3 68 2 := by decide +kernel
theorem cell_3_68_3 : CertificateAt 3 68 3 := by decide +kernel
theorem cell_3_68_4 : CertificateAt 3 68 4 := by decide +kernel
theorem cell_3_68_5 : CertificateAt 3 68 5 := by decide +kernel
theorem row_3_68 : ThresholdAt 3 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 68 0 cell_3_68_0
    | exact certificate_sound 3 68 1 cell_3_68_1
    | exact certificate_sound 3 68 2 cell_3_68_2
    | exact certificate_sound 3 68 3 cell_3_68_3
    | exact certificate_sound 3 68 4 cell_3_68_4
    | exact certificate_sound 3 68 5 cell_3_68_5
theorem cell_3_69_0 : CertificateAt 3 69 0 := by decide +kernel
theorem cell_3_69_1 : CertificateAt 3 69 1 := by decide +kernel
theorem cell_3_69_2 : CertificateAt 3 69 2 := by decide +kernel
theorem cell_3_69_3 : CertificateAt 3 69 3 := by decide +kernel
theorem cell_3_69_4 : CertificateAt 3 69 4 := by decide +kernel
theorem cell_3_69_5 : CertificateAt 3 69 5 := by decide +kernel
theorem row_3_69 : ThresholdAt 3 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 69 0 cell_3_69_0
    | exact certificate_sound 3 69 1 cell_3_69_1
    | exact certificate_sound 3 69 2 cell_3_69_2
    | exact certificate_sound 3 69 3 cell_3_69_3
    | exact certificate_sound 3 69 4 cell_3_69_4
    | exact certificate_sound 3 69 5 cell_3_69_5
theorem cell_3_70_0 : CertificateAt 3 70 0 := by decide +kernel
theorem cell_3_70_1 : CertificateAt 3 70 1 := by decide +kernel
theorem cell_3_70_2 : CertificateAt 3 70 2 := by decide +kernel
theorem cell_3_70_3 : CertificateAt 3 70 3 := by decide +kernel
theorem cell_3_70_4 : CertificateAt 3 70 4 := by decide +kernel
theorem cell_3_70_5 : CertificateAt 3 70 5 := by decide +kernel
theorem row_3_70 : ThresholdAt 3 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 70 0 cell_3_70_0
    | exact certificate_sound 3 70 1 cell_3_70_1
    | exact certificate_sound 3 70 2 cell_3_70_2
    | exact certificate_sound 3 70 3 cell_3_70_3
    | exact certificate_sound 3 70 4 cell_3_70_4
    | exact certificate_sound 3 70 5 cell_3_70_5
theorem cell_3_71_0 : CertificateAt 3 71 0 := by decide +kernel
theorem cell_3_71_1 : CertificateAt 3 71 1 := by decide +kernel
theorem cell_3_71_2 : CertificateAt 3 71 2 := by decide +kernel
theorem cell_3_71_3 : CertificateAt 3 71 3 := by decide +kernel
theorem cell_3_71_4 : CertificateAt 3 71 4 := by decide +kernel
theorem cell_3_71_5 : CertificateAt 3 71 5 := by decide +kernel
theorem row_3_71 : ThresholdAt 3 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 71 0 cell_3_71_0
    | exact certificate_sound 3 71 1 cell_3_71_1
    | exact certificate_sound 3 71 2 cell_3_71_2
    | exact certificate_sound 3 71 3 cell_3_71_3
    | exact certificate_sound 3 71 4 cell_3_71_4
    | exact certificate_sound 3 71 5 cell_3_71_5
theorem cell_3_72_0 : CertificateAt 3 72 0 := by decide +kernel
theorem cell_3_72_1 : CertificateAt 3 72 1 := by decide +kernel
theorem cell_3_72_2 : CertificateAt 3 72 2 := by decide +kernel
theorem cell_3_72_3 : CertificateAt 3 72 3 := by decide +kernel
theorem cell_3_72_4 : CertificateAt 3 72 4 := by decide +kernel
theorem cell_3_72_5 : CertificateAt 3 72 5 := by decide +kernel
theorem row_3_72 : ThresholdAt 3 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 72 0 cell_3_72_0
    | exact certificate_sound 3 72 1 cell_3_72_1
    | exact certificate_sound 3 72 2 cell_3_72_2
    | exact certificate_sound 3 72 3 cell_3_72_3
    | exact certificate_sound 3 72 4 cell_3_72_4
    | exact certificate_sound 3 72 5 cell_3_72_5
theorem cell_3_73_0 : CertificateAt 3 73 0 := by decide +kernel
theorem cell_3_73_1 : CertificateAt 3 73 1 := by decide +kernel
theorem cell_3_73_2 : CertificateAt 3 73 2 := by decide +kernel
theorem cell_3_73_3 : CertificateAt 3 73 3 := by decide +kernel
theorem cell_3_73_4 : CertificateAt 3 73 4 := by decide +kernel
theorem cell_3_73_5 : CertificateAt 3 73 5 := by decide +kernel
theorem row_3_73 : ThresholdAt 3 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 73 0 cell_3_73_0
    | exact certificate_sound 3 73 1 cell_3_73_1
    | exact certificate_sound 3 73 2 cell_3_73_2
    | exact certificate_sound 3 73 3 cell_3_73_3
    | exact certificate_sound 3 73 4 cell_3_73_4
    | exact certificate_sound 3 73 5 cell_3_73_5
theorem cell_3_74_0 : CertificateAt 3 74 0 := by decide +kernel
theorem cell_3_74_1 : CertificateAt 3 74 1 := by decide +kernel
theorem cell_3_74_2 : CertificateAt 3 74 2 := by decide +kernel
theorem cell_3_74_3 : CertificateAt 3 74 3 := by decide +kernel
theorem cell_3_74_4 : CertificateAt 3 74 4 := by decide +kernel
theorem cell_3_74_5 : CertificateAt 3 74 5 := by decide +kernel
theorem row_3_74 : ThresholdAt 3 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 74 0 cell_3_74_0
    | exact certificate_sound 3 74 1 cell_3_74_1
    | exact certificate_sound 3 74 2 cell_3_74_2
    | exact certificate_sound 3 74 3 cell_3_74_3
    | exact certificate_sound 3 74 4 cell_3_74_4
    | exact certificate_sound 3 74 5 cell_3_74_5
theorem cell_3_75_0 : CertificateAt 3 75 0 := by decide +kernel
theorem cell_3_75_1 : CertificateAt 3 75 1 := by decide +kernel
theorem cell_3_75_2 : CertificateAt 3 75 2 := by decide +kernel
theorem cell_3_75_3 : CertificateAt 3 75 3 := by decide +kernel
theorem cell_3_75_4 : CertificateAt 3 75 4 := by decide +kernel
theorem cell_3_75_5 : CertificateAt 3 75 5 := by decide +kernel
theorem row_3_75 : ThresholdAt 3 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 75 0 cell_3_75_0
    | exact certificate_sound 3 75 1 cell_3_75_1
    | exact certificate_sound 3 75 2 cell_3_75_2
    | exact certificate_sound 3 75 3 cell_3_75_3
    | exact certificate_sound 3 75 4 cell_3_75_4
    | exact certificate_sound 3 75 5 cell_3_75_5
theorem cell_3_76_0 : CertificateAt 3 76 0 := by decide +kernel
theorem cell_3_76_1 : CertificateAt 3 76 1 := by decide +kernel
theorem cell_3_76_2 : CertificateAt 3 76 2 := by decide +kernel
theorem cell_3_76_3 : CertificateAt 3 76 3 := by decide +kernel
theorem cell_3_76_4 : CertificateAt 3 76 4 := by decide +kernel
theorem cell_3_76_5 : CertificateAt 3 76 5 := by decide +kernel
theorem row_3_76 : ThresholdAt 3 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 76 0 cell_3_76_0
    | exact certificate_sound 3 76 1 cell_3_76_1
    | exact certificate_sound 3 76 2 cell_3_76_2
    | exact certificate_sound 3 76 3 cell_3_76_3
    | exact certificate_sound 3 76 4 cell_3_76_4
    | exact certificate_sound 3 76 5 cell_3_76_5
theorem cell_3_77_0 : CertificateAt 3 77 0 := by decide +kernel
theorem cell_3_77_1 : CertificateAt 3 77 1 := by decide +kernel
theorem cell_3_77_2 : CertificateAt 3 77 2 := by decide +kernel
theorem cell_3_77_3 : CertificateAt 3 77 3 := by decide +kernel
theorem cell_3_77_4 : CertificateAt 3 77 4 := by decide +kernel
theorem cell_3_77_5 : CertificateAt 3 77 5 := by decide +kernel
theorem row_3_77 : ThresholdAt 3 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 77 0 cell_3_77_0
    | exact certificate_sound 3 77 1 cell_3_77_1
    | exact certificate_sound 3 77 2 cell_3_77_2
    | exact certificate_sound 3 77 3 cell_3_77_3
    | exact certificate_sound 3 77 4 cell_3_77_4
    | exact certificate_sound 3 77 5 cell_3_77_5
theorem cell_3_78_0 : CertificateAt 3 78 0 := by decide +kernel
theorem cell_3_78_1 : CertificateAt 3 78 1 := by decide +kernel
theorem cell_3_78_2 : CertificateAt 3 78 2 := by decide +kernel
theorem cell_3_78_3 : CertificateAt 3 78 3 := by decide +kernel
theorem cell_3_78_4 : CertificateAt 3 78 4 := by decide +kernel
theorem cell_3_78_5 : CertificateAt 3 78 5 := by decide +kernel
theorem row_3_78 : ThresholdAt 3 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 78 0 cell_3_78_0
    | exact certificate_sound 3 78 1 cell_3_78_1
    | exact certificate_sound 3 78 2 cell_3_78_2
    | exact certificate_sound 3 78 3 cell_3_78_3
    | exact certificate_sound 3 78 4 cell_3_78_4
    | exact certificate_sound 3 78 5 cell_3_78_5
theorem cell_3_79_0 : CertificateAt 3 79 0 := by decide +kernel
theorem cell_3_79_1 : CertificateAt 3 79 1 := by decide +kernel
theorem cell_3_79_2 : CertificateAt 3 79 2 := by decide +kernel
theorem cell_3_79_3 : CertificateAt 3 79 3 := by decide +kernel
theorem cell_3_79_4 : CertificateAt 3 79 4 := by decide +kernel
theorem cell_3_79_5 : CertificateAt 3 79 5 := by decide +kernel
theorem row_3_79 : ThresholdAt 3 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 79 0 cell_3_79_0
    | exact certificate_sound 3 79 1 cell_3_79_1
    | exact certificate_sound 3 79 2 cell_3_79_2
    | exact certificate_sound 3 79 3 cell_3_79_3
    | exact certificate_sound 3 79 4 cell_3_79_4
    | exact certificate_sound 3 79 5 cell_3_79_5
theorem cell_3_80_0 : CertificateAt 3 80 0 := by decide +kernel
theorem cell_3_80_1 : CertificateAt 3 80 1 := by decide +kernel
theorem cell_3_80_2 : CertificateAt 3 80 2 := by decide +kernel
theorem cell_3_80_3 : CertificateAt 3 80 3 := by decide +kernel
theorem cell_3_80_4 : CertificateAt 3 80 4 := by decide +kernel
theorem cell_3_80_5 : CertificateAt 3 80 5 := by decide +kernel
theorem row_3_80 : ThresholdAt 3 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 80 0 cell_3_80_0
    | exact certificate_sound 3 80 1 cell_3_80_1
    | exact certificate_sound 3 80 2 cell_3_80_2
    | exact certificate_sound 3 80 3 cell_3_80_3
    | exact certificate_sound 3 80 4 cell_3_80_4
    | exact certificate_sound 3 80 5 cell_3_80_5
theorem cell_3_81_0 : CertificateAt 3 81 0 := by decide +kernel
theorem cell_3_81_1 : CertificateAt 3 81 1 := by decide +kernel
theorem cell_3_81_2 : CertificateAt 3 81 2 := by decide +kernel
theorem cell_3_81_3 : CertificateAt 3 81 3 := by decide +kernel
theorem cell_3_81_4 : CertificateAt 3 81 4 := by decide +kernel
theorem cell_3_81_5 : CertificateAt 3 81 5 := by decide +kernel
theorem row_3_81 : ThresholdAt 3 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 81 0 cell_3_81_0
    | exact certificate_sound 3 81 1 cell_3_81_1
    | exact certificate_sound 3 81 2 cell_3_81_2
    | exact certificate_sound 3 81 3 cell_3_81_3
    | exact certificate_sound 3 81 4 cell_3_81_4
    | exact certificate_sound 3 81 5 cell_3_81_5
theorem cell_3_82_0 : CertificateAt 3 82 0 := by decide +kernel
theorem cell_3_82_1 : CertificateAt 3 82 1 := by decide +kernel
theorem cell_3_82_2 : CertificateAt 3 82 2 := by decide +kernel
theorem cell_3_82_3 : CertificateAt 3 82 3 := by decide +kernel
theorem cell_3_82_4 : CertificateAt 3 82 4 := by decide +kernel
theorem cell_3_82_5 : CertificateAt 3 82 5 := by decide +kernel
theorem row_3_82 : ThresholdAt 3 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 82 0 cell_3_82_0
    | exact certificate_sound 3 82 1 cell_3_82_1
    | exact certificate_sound 3 82 2 cell_3_82_2
    | exact certificate_sound 3 82 3 cell_3_82_3
    | exact certificate_sound 3 82 4 cell_3_82_4
    | exact certificate_sound 3 82 5 cell_3_82_5
theorem cell_3_83_0 : CertificateAt 3 83 0 := by decide +kernel
theorem cell_3_83_1 : CertificateAt 3 83 1 := by decide +kernel
theorem cell_3_83_2 : CertificateAt 3 83 2 := by decide +kernel
theorem cell_3_83_3 : CertificateAt 3 83 3 := by decide +kernel
theorem cell_3_83_4 : CertificateAt 3 83 4 := by decide +kernel
theorem cell_3_83_5 : CertificateAt 3 83 5 := by decide +kernel
theorem row_3_83 : ThresholdAt 3 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 83 0 cell_3_83_0
    | exact certificate_sound 3 83 1 cell_3_83_1
    | exact certificate_sound 3 83 2 cell_3_83_2
    | exact certificate_sound 3 83 3 cell_3_83_3
    | exact certificate_sound 3 83 4 cell_3_83_4
    | exact certificate_sound 3 83 5 cell_3_83_5
theorem cell_3_84_0 : CertificateAt 3 84 0 := by decide +kernel
theorem cell_3_84_1 : CertificateAt 3 84 1 := by decide +kernel
theorem cell_3_84_2 : CertificateAt 3 84 2 := by decide +kernel
theorem cell_3_84_3 : CertificateAt 3 84 3 := by decide +kernel
theorem cell_3_84_4 : CertificateAt 3 84 4 := by decide +kernel
theorem cell_3_84_5 : CertificateAt 3 84 5 := by decide +kernel
theorem row_3_84 : ThresholdAt 3 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 84 0 cell_3_84_0
    | exact certificate_sound 3 84 1 cell_3_84_1
    | exact certificate_sound 3 84 2 cell_3_84_2
    | exact certificate_sound 3 84 3 cell_3_84_3
    | exact certificate_sound 3 84 4 cell_3_84_4
    | exact certificate_sound 3 84 5 cell_3_84_5
theorem cell_3_85_0 : CertificateAt 3 85 0 := by decide +kernel
theorem cell_3_85_1 : CertificateAt 3 85 1 := by decide +kernel
theorem cell_3_85_2 : CertificateAt 3 85 2 := by decide +kernel
theorem cell_3_85_3 : CertificateAt 3 85 3 := by decide +kernel
theorem cell_3_85_4 : CertificateAt 3 85 4 := by decide +kernel
theorem cell_3_85_5 : CertificateAt 3 85 5 := by decide +kernel
theorem row_3_85 : ThresholdAt 3 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 85 0 cell_3_85_0
    | exact certificate_sound 3 85 1 cell_3_85_1
    | exact certificate_sound 3 85 2 cell_3_85_2
    | exact certificate_sound 3 85 3 cell_3_85_3
    | exact certificate_sound 3 85 4 cell_3_85_4
    | exact certificate_sound 3 85 5 cell_3_85_5
theorem cell_3_86_0 : CertificateAt 3 86 0 := by decide +kernel
theorem cell_3_86_1 : CertificateAt 3 86 1 := by decide +kernel
theorem cell_3_86_2 : CertificateAt 3 86 2 := by decide +kernel
theorem cell_3_86_3 : CertificateAt 3 86 3 := by decide +kernel
theorem cell_3_86_4 : CertificateAt 3 86 4 := by decide +kernel
theorem cell_3_86_5 : CertificateAt 3 86 5 := by decide +kernel
theorem row_3_86 : ThresholdAt 3 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 86 0 cell_3_86_0
    | exact certificate_sound 3 86 1 cell_3_86_1
    | exact certificate_sound 3 86 2 cell_3_86_2
    | exact certificate_sound 3 86 3 cell_3_86_3
    | exact certificate_sound 3 86 4 cell_3_86_4
    | exact certificate_sound 3 86 5 cell_3_86_5
theorem cell_3_87_0 : CertificateAt 3 87 0 := by decide +kernel
theorem cell_3_87_1 : CertificateAt 3 87 1 := by decide +kernel
theorem cell_3_87_2 : CertificateAt 3 87 2 := by decide +kernel
theorem cell_3_87_3 : CertificateAt 3 87 3 := by decide +kernel
theorem cell_3_87_4 : CertificateAt 3 87 4 := by decide +kernel
theorem cell_3_87_5 : CertificateAt 3 87 5 := by decide +kernel
theorem row_3_87 : ThresholdAt 3 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 87 0 cell_3_87_0
    | exact certificate_sound 3 87 1 cell_3_87_1
    | exact certificate_sound 3 87 2 cell_3_87_2
    | exact certificate_sound 3 87 3 cell_3_87_3
    | exact certificate_sound 3 87 4 cell_3_87_4
    | exact certificate_sound 3 87 5 cell_3_87_5
theorem cell_3_88_0 : CertificateAt 3 88 0 := by decide +kernel
theorem cell_3_88_1 : CertificateAt 3 88 1 := by decide +kernel
theorem cell_3_88_2 : CertificateAt 3 88 2 := by decide +kernel
theorem cell_3_88_3 : CertificateAt 3 88 3 := by decide +kernel
theorem cell_3_88_4 : CertificateAt 3 88 4 := by decide +kernel
theorem cell_3_88_5 : CertificateAt 3 88 5 := by decide +kernel
theorem row_3_88 : ThresholdAt 3 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 88 0 cell_3_88_0
    | exact certificate_sound 3 88 1 cell_3_88_1
    | exact certificate_sound 3 88 2 cell_3_88_2
    | exact certificate_sound 3 88 3 cell_3_88_3
    | exact certificate_sound 3 88 4 cell_3_88_4
    | exact certificate_sound 3 88 5 cell_3_88_5
theorem cell_3_89_0 : CertificateAt 3 89 0 := by decide +kernel
theorem cell_3_89_1 : CertificateAt 3 89 1 := by decide +kernel
theorem cell_3_89_2 : CertificateAt 3 89 2 := by decide +kernel
theorem cell_3_89_3 : CertificateAt 3 89 3 := by decide +kernel
theorem cell_3_89_4 : CertificateAt 3 89 4 := by decide +kernel
theorem cell_3_89_5 : CertificateAt 3 89 5 := by decide +kernel
theorem row_3_89 : ThresholdAt 3 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 89 0 cell_3_89_0
    | exact certificate_sound 3 89 1 cell_3_89_1
    | exact certificate_sound 3 89 2 cell_3_89_2
    | exact certificate_sound 3 89 3 cell_3_89_3
    | exact certificate_sound 3 89 4 cell_3_89_4
    | exact certificate_sound 3 89 5 cell_3_89_5
theorem cell_3_90_0 : CertificateAt 3 90 0 := by decide +kernel
theorem cell_3_90_1 : CertificateAt 3 90 1 := by decide +kernel
theorem cell_3_90_2 : CertificateAt 3 90 2 := by decide +kernel
theorem cell_3_90_3 : CertificateAt 3 90 3 := by decide +kernel
theorem cell_3_90_4 : CertificateAt 3 90 4 := by decide +kernel
theorem cell_3_90_5 : CertificateAt 3 90 5 := by decide +kernel
theorem row_3_90 : ThresholdAt 3 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 90 0 cell_3_90_0
    | exact certificate_sound 3 90 1 cell_3_90_1
    | exact certificate_sound 3 90 2 cell_3_90_2
    | exact certificate_sound 3 90 3 cell_3_90_3
    | exact certificate_sound 3 90 4 cell_3_90_4
    | exact certificate_sound 3 90 5 cell_3_90_5
theorem cell_3_91_0 : CertificateAt 3 91 0 := by decide +kernel
theorem cell_3_91_1 : CertificateAt 3 91 1 := by decide +kernel
theorem cell_3_91_2 : CertificateAt 3 91 2 := by decide +kernel
theorem cell_3_91_3 : CertificateAt 3 91 3 := by decide +kernel
theorem cell_3_91_4 : CertificateAt 3 91 4 := by decide +kernel
theorem cell_3_91_5 : CertificateAt 3 91 5 := by decide +kernel
theorem row_3_91 : ThresholdAt 3 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 91 0 cell_3_91_0
    | exact certificate_sound 3 91 1 cell_3_91_1
    | exact certificate_sound 3 91 2 cell_3_91_2
    | exact certificate_sound 3 91 3 cell_3_91_3
    | exact certificate_sound 3 91 4 cell_3_91_4
    | exact certificate_sound 3 91 5 cell_3_91_5
theorem cell_3_92_0 : CertificateAt 3 92 0 := by decide +kernel
theorem cell_3_92_1 : CertificateAt 3 92 1 := by decide +kernel
theorem cell_3_92_2 : CertificateAt 3 92 2 := by decide +kernel
theorem cell_3_92_3 : CertificateAt 3 92 3 := by decide +kernel
theorem cell_3_92_4 : CertificateAt 3 92 4 := by decide +kernel
theorem cell_3_92_5 : CertificateAt 3 92 5 := by decide +kernel
theorem row_3_92 : ThresholdAt 3 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 92 0 cell_3_92_0
    | exact certificate_sound 3 92 1 cell_3_92_1
    | exact certificate_sound 3 92 2 cell_3_92_2
    | exact certificate_sound 3 92 3 cell_3_92_3
    | exact certificate_sound 3 92 4 cell_3_92_4
    | exact certificate_sound 3 92 5 cell_3_92_5
theorem cell_3_93_0 : CertificateAt 3 93 0 := by decide +kernel
theorem cell_3_93_1 : CertificateAt 3 93 1 := by decide +kernel
theorem cell_3_93_2 : CertificateAt 3 93 2 := by decide +kernel
theorem cell_3_93_3 : CertificateAt 3 93 3 := by decide +kernel
theorem cell_3_93_4 : CertificateAt 3 93 4 := by decide +kernel
theorem cell_3_93_5 : CertificateAt 3 93 5 := by decide +kernel
theorem row_3_93 : ThresholdAt 3 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 93 0 cell_3_93_0
    | exact certificate_sound 3 93 1 cell_3_93_1
    | exact certificate_sound 3 93 2 cell_3_93_2
    | exact certificate_sound 3 93 3 cell_3_93_3
    | exact certificate_sound 3 93 4 cell_3_93_4
    | exact certificate_sound 3 93 5 cell_3_93_5
theorem cell_3_94_0 : CertificateAt 3 94 0 := by decide +kernel
theorem cell_3_94_1 : CertificateAt 3 94 1 := by decide +kernel
theorem cell_3_94_2 : CertificateAt 3 94 2 := by decide +kernel
theorem cell_3_94_3 : CertificateAt 3 94 3 := by decide +kernel
theorem cell_3_94_4 : CertificateAt 3 94 4 := by decide +kernel
theorem cell_3_94_5 : CertificateAt 3 94 5 := by decide +kernel
theorem row_3_94 : ThresholdAt 3 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 94 0 cell_3_94_0
    | exact certificate_sound 3 94 1 cell_3_94_1
    | exact certificate_sound 3 94 2 cell_3_94_2
    | exact certificate_sound 3 94 3 cell_3_94_3
    | exact certificate_sound 3 94 4 cell_3_94_4
    | exact certificate_sound 3 94 5 cell_3_94_5
theorem cell_3_95_0 : CertificateAt 3 95 0 := by decide +kernel
theorem cell_3_95_1 : CertificateAt 3 95 1 := by decide +kernel
theorem cell_3_95_2 : CertificateAt 3 95 2 := by decide +kernel
theorem cell_3_95_3 : CertificateAt 3 95 3 := by decide +kernel
theorem cell_3_95_4 : CertificateAt 3 95 4 := by decide +kernel
theorem cell_3_95_5 : CertificateAt 3 95 5 := by decide +kernel
theorem row_3_95 : ThresholdAt 3 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 95 0 cell_3_95_0
    | exact certificate_sound 3 95 1 cell_3_95_1
    | exact certificate_sound 3 95 2 cell_3_95_2
    | exact certificate_sound 3 95 3 cell_3_95_3
    | exact certificate_sound 3 95 4 cell_3_95_4
    | exact certificate_sound 3 95 5 cell_3_95_5
theorem cell_3_96_0 : CertificateAt 3 96 0 := by decide +kernel
theorem cell_3_96_1 : CertificateAt 3 96 1 := by decide +kernel
theorem cell_3_96_2 : CertificateAt 3 96 2 := by decide +kernel
theorem cell_3_96_3 : CertificateAt 3 96 3 := by decide +kernel
theorem cell_3_96_4 : CertificateAt 3 96 4 := by decide +kernel
theorem cell_3_96_5 : CertificateAt 3 96 5 := by decide +kernel
theorem row_3_96 : ThresholdAt 3 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 96 0 cell_3_96_0
    | exact certificate_sound 3 96 1 cell_3_96_1
    | exact certificate_sound 3 96 2 cell_3_96_2
    | exact certificate_sound 3 96 3 cell_3_96_3
    | exact certificate_sound 3 96 4 cell_3_96_4
    | exact certificate_sound 3 96 5 cell_3_96_5
theorem cell_3_97_0 : CertificateAt 3 97 0 := by decide +kernel
theorem cell_3_97_1 : CertificateAt 3 97 1 := by decide +kernel
theorem cell_3_97_2 : CertificateAt 3 97 2 := by decide +kernel
theorem cell_3_97_3 : CertificateAt 3 97 3 := by decide +kernel
theorem cell_3_97_4 : CertificateAt 3 97 4 := by decide +kernel
theorem cell_3_97_5 : CertificateAt 3 97 5 := by decide +kernel
theorem row_3_97 : ThresholdAt 3 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 97 0 cell_3_97_0
    | exact certificate_sound 3 97 1 cell_3_97_1
    | exact certificate_sound 3 97 2 cell_3_97_2
    | exact certificate_sound 3 97 3 cell_3_97_3
    | exact certificate_sound 3 97 4 cell_3_97_4
    | exact certificate_sound 3 97 5 cell_3_97_5
theorem cell_3_98_0 : CertificateAt 3 98 0 := by decide +kernel
theorem cell_3_98_1 : CertificateAt 3 98 1 := by decide +kernel
theorem cell_3_98_2 : CertificateAt 3 98 2 := by decide +kernel
theorem cell_3_98_3 : CertificateAt 3 98 3 := by decide +kernel
theorem cell_3_98_4 : CertificateAt 3 98 4 := by decide +kernel
theorem cell_3_98_5 : CertificateAt 3 98 5 := by decide +kernel
theorem row_3_98 : ThresholdAt 3 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 98 0 cell_3_98_0
    | exact certificate_sound 3 98 1 cell_3_98_1
    | exact certificate_sound 3 98 2 cell_3_98_2
    | exact certificate_sound 3 98 3 cell_3_98_3
    | exact certificate_sound 3 98 4 cell_3_98_4
    | exact certificate_sound 3 98 5 cell_3_98_5
theorem cell_3_99_0 : CertificateAt 3 99 0 := by decide +kernel
theorem cell_3_99_1 : CertificateAt 3 99 1 := by decide +kernel
theorem cell_3_99_2 : CertificateAt 3 99 2 := by decide +kernel
theorem cell_3_99_3 : CertificateAt 3 99 3 := by decide +kernel
theorem cell_3_99_4 : CertificateAt 3 99 4 := by decide +kernel
theorem cell_3_99_5 : CertificateAt 3 99 5 := by decide +kernel
theorem row_3_99 : ThresholdAt 3 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 99 0 cell_3_99_0
    | exact certificate_sound 3 99 1 cell_3_99_1
    | exact certificate_sound 3 99 2 cell_3_99_2
    | exact certificate_sound 3 99 3 cell_3_99_3
    | exact certificate_sound 3 99 4 cell_3_99_4
    | exact certificate_sound 3 99 5 cell_3_99_5
theorem cell_3_100_0 : CertificateAt 3 100 0 := by decide +kernel
theorem cell_3_100_1 : CertificateAt 3 100 1 := by decide +kernel
theorem cell_3_100_2 : CertificateAt 3 100 2 := by decide +kernel
theorem cell_3_100_3 : CertificateAt 3 100 3 := by decide +kernel
theorem cell_3_100_4 : CertificateAt 3 100 4 := by decide +kernel
theorem cell_3_100_5 : CertificateAt 3 100 5 := by decide +kernel
theorem row_3_100 : ThresholdAt 3 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 100 0 cell_3_100_0
    | exact certificate_sound 3 100 1 cell_3_100_1
    | exact certificate_sound 3 100 2 cell_3_100_2
    | exact certificate_sound 3 100 3 cell_3_100_3
    | exact certificate_sound 3 100 4 cell_3_100_4
    | exact certificate_sound 3 100 5 cell_3_100_5
theorem cell_3_101_0 : CertificateAt 3 101 0 := by decide +kernel
theorem cell_3_101_1 : CertificateAt 3 101 1 := by decide +kernel
theorem cell_3_101_2 : CertificateAt 3 101 2 := by decide +kernel
theorem cell_3_101_3 : CertificateAt 3 101 3 := by decide +kernel
theorem cell_3_101_4 : CertificateAt 3 101 4 := by decide +kernel
theorem cell_3_101_5 : CertificateAt 3 101 5 := by decide +kernel
theorem row_3_101 : ThresholdAt 3 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 101 0 cell_3_101_0
    | exact certificate_sound 3 101 1 cell_3_101_1
    | exact certificate_sound 3 101 2 cell_3_101_2
    | exact certificate_sound 3 101 3 cell_3_101_3
    | exact certificate_sound 3 101 4 cell_3_101_4
    | exact certificate_sound 3 101 5 cell_3_101_5
theorem cell_3_102_0 : CertificateAt 3 102 0 := by decide +kernel
theorem cell_3_102_1 : CertificateAt 3 102 1 := by decide +kernel
theorem cell_3_102_2 : CertificateAt 3 102 2 := by decide +kernel
theorem cell_3_102_3 : CertificateAt 3 102 3 := by decide +kernel
theorem cell_3_102_4 : CertificateAt 3 102 4 := by decide +kernel
theorem cell_3_102_5 : CertificateAt 3 102 5 := by decide +kernel
theorem row_3_102 : ThresholdAt 3 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 102 0 cell_3_102_0
    | exact certificate_sound 3 102 1 cell_3_102_1
    | exact certificate_sound 3 102 2 cell_3_102_2
    | exact certificate_sound 3 102 3 cell_3_102_3
    | exact certificate_sound 3 102 4 cell_3_102_4
    | exact certificate_sound 3 102 5 cell_3_102_5
theorem cell_3_103_0 : CertificateAt 3 103 0 := by decide +kernel
theorem cell_3_103_1 : CertificateAt 3 103 1 := by decide +kernel
theorem cell_3_103_2 : CertificateAt 3 103 2 := by decide +kernel
theorem cell_3_103_3 : CertificateAt 3 103 3 := by decide +kernel
theorem cell_3_103_4 : CertificateAt 3 103 4 := by decide +kernel
theorem cell_3_103_5 : CertificateAt 3 103 5 := by decide +kernel
theorem row_3_103 : ThresholdAt 3 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 103 0 cell_3_103_0
    | exact certificate_sound 3 103 1 cell_3_103_1
    | exact certificate_sound 3 103 2 cell_3_103_2
    | exact certificate_sound 3 103 3 cell_3_103_3
    | exact certificate_sound 3 103 4 cell_3_103_4
    | exact certificate_sound 3 103 5 cell_3_103_5
theorem cell_3_104_0 : CertificateAt 3 104 0 := by decide +kernel
theorem cell_3_104_1 : CertificateAt 3 104 1 := by decide +kernel
theorem cell_3_104_2 : CertificateAt 3 104 2 := by decide +kernel
theorem cell_3_104_3 : CertificateAt 3 104 3 := by decide +kernel
theorem cell_3_104_4 : CertificateAt 3 104 4 := by decide +kernel
theorem cell_3_104_5 : CertificateAt 3 104 5 := by decide +kernel
theorem row_3_104 : ThresholdAt 3 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 104 0 cell_3_104_0
    | exact certificate_sound 3 104 1 cell_3_104_1
    | exact certificate_sound 3 104 2 cell_3_104_2
    | exact certificate_sound 3 104 3 cell_3_104_3
    | exact certificate_sound 3 104 4 cell_3_104_4
    | exact certificate_sound 3 104 5 cell_3_104_5
theorem cell_3_105_0 : CertificateAt 3 105 0 := by decide +kernel
theorem cell_3_105_1 : CertificateAt 3 105 1 := by decide +kernel
theorem cell_3_105_2 : CertificateAt 3 105 2 := by decide +kernel
theorem cell_3_105_3 : CertificateAt 3 105 3 := by decide +kernel
theorem cell_3_105_4 : CertificateAt 3 105 4 := by decide +kernel
theorem cell_3_105_5 : CertificateAt 3 105 5 := by decide +kernel
theorem row_3_105 : ThresholdAt 3 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 105 0 cell_3_105_0
    | exact certificate_sound 3 105 1 cell_3_105_1
    | exact certificate_sound 3 105 2 cell_3_105_2
    | exact certificate_sound 3 105 3 cell_3_105_3
    | exact certificate_sound 3 105 4 cell_3_105_4
    | exact certificate_sound 3 105 5 cell_3_105_5
theorem cell_3_106_0 : CertificateAt 3 106 0 := by decide +kernel
theorem cell_3_106_1 : CertificateAt 3 106 1 := by decide +kernel
theorem cell_3_106_2 : CertificateAt 3 106 2 := by decide +kernel
theorem cell_3_106_3 : CertificateAt 3 106 3 := by decide +kernel
theorem cell_3_106_4 : CertificateAt 3 106 4 := by decide +kernel
theorem cell_3_106_5 : CertificateAt 3 106 5 := by decide +kernel
theorem row_3_106 : ThresholdAt 3 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 106 0 cell_3_106_0
    | exact certificate_sound 3 106 1 cell_3_106_1
    | exact certificate_sound 3 106 2 cell_3_106_2
    | exact certificate_sound 3 106 3 cell_3_106_3
    | exact certificate_sound 3 106 4 cell_3_106_4
    | exact certificate_sound 3 106 5 cell_3_106_5
theorem cell_3_107_0 : CertificateAt 3 107 0 := by decide +kernel
theorem cell_3_107_1 : CertificateAt 3 107 1 := by decide +kernel
theorem cell_3_107_2 : CertificateAt 3 107 2 := by decide +kernel
theorem cell_3_107_3 : CertificateAt 3 107 3 := by decide +kernel
theorem cell_3_107_4 : CertificateAt 3 107 4 := by decide +kernel
theorem cell_3_107_5 : CertificateAt 3 107 5 := by decide +kernel
theorem row_3_107 : ThresholdAt 3 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 107 0 cell_3_107_0
    | exact certificate_sound 3 107 1 cell_3_107_1
    | exact certificate_sound 3 107 2 cell_3_107_2
    | exact certificate_sound 3 107 3 cell_3_107_3
    | exact certificate_sound 3 107 4 cell_3_107_4
    | exact certificate_sound 3 107 5 cell_3_107_5
theorem cell_3_108_0 : CertificateAt 3 108 0 := by decide +kernel
theorem cell_3_108_1 : CertificateAt 3 108 1 := by decide +kernel
theorem cell_3_108_2 : CertificateAt 3 108 2 := by decide +kernel
theorem cell_3_108_3 : CertificateAt 3 108 3 := by decide +kernel
theorem cell_3_108_4 : CertificateAt 3 108 4 := by decide +kernel
theorem cell_3_108_5 : CertificateAt 3 108 5 := by decide +kernel
theorem row_3_108 : ThresholdAt 3 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 108 0 cell_3_108_0
    | exact certificate_sound 3 108 1 cell_3_108_1
    | exact certificate_sound 3 108 2 cell_3_108_2
    | exact certificate_sound 3 108 3 cell_3_108_3
    | exact certificate_sound 3 108 4 cell_3_108_4
    | exact certificate_sound 3 108 5 cell_3_108_5
theorem cell_3_109_0 : CertificateAt 3 109 0 := by decide +kernel
theorem cell_3_109_1 : CertificateAt 3 109 1 := by decide +kernel
theorem cell_3_109_2 : CertificateAt 3 109 2 := by decide +kernel
theorem cell_3_109_3 : CertificateAt 3 109 3 := by decide +kernel
theorem cell_3_109_4 : CertificateAt 3 109 4 := by decide +kernel
theorem cell_3_109_5 : CertificateAt 3 109 5 := by decide +kernel
theorem row_3_109 : ThresholdAt 3 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 109 0 cell_3_109_0
    | exact certificate_sound 3 109 1 cell_3_109_1
    | exact certificate_sound 3 109 2 cell_3_109_2
    | exact certificate_sound 3 109 3 cell_3_109_3
    | exact certificate_sound 3 109 4 cell_3_109_4
    | exact certificate_sound 3 109 5 cell_3_109_5
theorem cell_3_110_0 : CertificateAt 3 110 0 := by decide +kernel
theorem cell_3_110_1 : CertificateAt 3 110 1 := by decide +kernel
theorem cell_3_110_2 : CertificateAt 3 110 2 := by decide +kernel
theorem cell_3_110_3 : CertificateAt 3 110 3 := by decide +kernel
theorem cell_3_110_4 : CertificateAt 3 110 4 := by decide +kernel
theorem cell_3_110_5 : CertificateAt 3 110 5 := by decide +kernel
theorem row_3_110 : ThresholdAt 3 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 110 0 cell_3_110_0
    | exact certificate_sound 3 110 1 cell_3_110_1
    | exact certificate_sound 3 110 2 cell_3_110_2
    | exact certificate_sound 3 110 3 cell_3_110_3
    | exact certificate_sound 3 110 4 cell_3_110_4
    | exact certificate_sound 3 110 5 cell_3_110_5
theorem cell_3_111_0 : CertificateAt 3 111 0 := by decide +kernel
theorem cell_3_111_1 : CertificateAt 3 111 1 := by decide +kernel
theorem cell_3_111_2 : CertificateAt 3 111 2 := by decide +kernel
theorem cell_3_111_3 : CertificateAt 3 111 3 := by decide +kernel
theorem cell_3_111_4 : CertificateAt 3 111 4 := by decide +kernel
theorem cell_3_111_5 : CertificateAt 3 111 5 := by decide +kernel
theorem row_3_111 : ThresholdAt 3 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 111 0 cell_3_111_0
    | exact certificate_sound 3 111 1 cell_3_111_1
    | exact certificate_sound 3 111 2 cell_3_111_2
    | exact certificate_sound 3 111 3 cell_3_111_3
    | exact certificate_sound 3 111 4 cell_3_111_4
    | exact certificate_sound 3 111 5 cell_3_111_5
theorem cell_3_112_0 : CertificateAt 3 112 0 := by decide +kernel
theorem cell_3_112_1 : CertificateAt 3 112 1 := by decide +kernel
theorem cell_3_112_2 : CertificateAt 3 112 2 := by decide +kernel
theorem cell_3_112_3 : CertificateAt 3 112 3 := by decide +kernel
theorem cell_3_112_4 : CertificateAt 3 112 4 := by decide +kernel
theorem cell_3_112_5 : CertificateAt 3 112 5 := by decide +kernel
theorem row_3_112 : ThresholdAt 3 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 112 0 cell_3_112_0
    | exact certificate_sound 3 112 1 cell_3_112_1
    | exact certificate_sound 3 112 2 cell_3_112_2
    | exact certificate_sound 3 112 3 cell_3_112_3
    | exact certificate_sound 3 112 4 cell_3_112_4
    | exact certificate_sound 3 112 5 cell_3_112_5
theorem cell_3_113_0 : CertificateAt 3 113 0 := by decide +kernel
theorem cell_3_113_1 : CertificateAt 3 113 1 := by decide +kernel
theorem cell_3_113_2 : CertificateAt 3 113 2 := by decide +kernel
theorem cell_3_113_3 : CertificateAt 3 113 3 := by decide +kernel
theorem cell_3_113_4 : CertificateAt 3 113 4 := by decide +kernel
theorem cell_3_113_5 : CertificateAt 3 113 5 := by decide +kernel
theorem row_3_113 : ThresholdAt 3 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 113 0 cell_3_113_0
    | exact certificate_sound 3 113 1 cell_3_113_1
    | exact certificate_sound 3 113 2 cell_3_113_2
    | exact certificate_sound 3 113 3 cell_3_113_3
    | exact certificate_sound 3 113 4 cell_3_113_4
    | exact certificate_sound 3 113 5 cell_3_113_5
theorem cell_3_114_0 : CertificateAt 3 114 0 := by decide +kernel
theorem cell_3_114_1 : CertificateAt 3 114 1 := by decide +kernel
theorem cell_3_114_2 : CertificateAt 3 114 2 := by decide +kernel
theorem cell_3_114_3 : CertificateAt 3 114 3 := by decide +kernel
theorem cell_3_114_4 : CertificateAt 3 114 4 := by decide +kernel
theorem cell_3_114_5 : CertificateAt 3 114 5 := by decide +kernel
theorem row_3_114 : ThresholdAt 3 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 114 0 cell_3_114_0
    | exact certificate_sound 3 114 1 cell_3_114_1
    | exact certificate_sound 3 114 2 cell_3_114_2
    | exact certificate_sound 3 114 3 cell_3_114_3
    | exact certificate_sound 3 114 4 cell_3_114_4
    | exact certificate_sound 3 114 5 cell_3_114_5
theorem cell_3_115_0 : CertificateAt 3 115 0 := by decide +kernel
theorem cell_3_115_1 : CertificateAt 3 115 1 := by decide +kernel
theorem cell_3_115_2 : CertificateAt 3 115 2 := by decide +kernel
theorem cell_3_115_3 : CertificateAt 3 115 3 := by decide +kernel
theorem cell_3_115_4 : CertificateAt 3 115 4 := by decide +kernel
theorem cell_3_115_5 : CertificateAt 3 115 5 := by decide +kernel
theorem row_3_115 : ThresholdAt 3 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 115 0 cell_3_115_0
    | exact certificate_sound 3 115 1 cell_3_115_1
    | exact certificate_sound 3 115 2 cell_3_115_2
    | exact certificate_sound 3 115 3 cell_3_115_3
    | exact certificate_sound 3 115 4 cell_3_115_4
    | exact certificate_sound 3 115 5 cell_3_115_5
theorem cell_3_116_0 : CertificateAt 3 116 0 := by decide +kernel
theorem cell_3_116_1 : CertificateAt 3 116 1 := by decide +kernel
theorem cell_3_116_2 : CertificateAt 3 116 2 := by decide +kernel
theorem cell_3_116_3 : CertificateAt 3 116 3 := by decide +kernel
theorem cell_3_116_4 : CertificateAt 3 116 4 := by decide +kernel
theorem cell_3_116_5 : CertificateAt 3 116 5 := by decide +kernel
theorem row_3_116 : ThresholdAt 3 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 116 0 cell_3_116_0
    | exact certificate_sound 3 116 1 cell_3_116_1
    | exact certificate_sound 3 116 2 cell_3_116_2
    | exact certificate_sound 3 116 3 cell_3_116_3
    | exact certificate_sound 3 116 4 cell_3_116_4
    | exact certificate_sound 3 116 5 cell_3_116_5
theorem cell_3_117_0 : CertificateAt 3 117 0 := by decide +kernel
theorem cell_3_117_1 : CertificateAt 3 117 1 := by decide +kernel
theorem cell_3_117_2 : CertificateAt 3 117 2 := by decide +kernel
theorem cell_3_117_3 : CertificateAt 3 117 3 := by decide +kernel
theorem cell_3_117_4 : CertificateAt 3 117 4 := by decide +kernel
theorem cell_3_117_5 : CertificateAt 3 117 5 := by decide +kernel
theorem row_3_117 : ThresholdAt 3 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 117 0 cell_3_117_0
    | exact certificate_sound 3 117 1 cell_3_117_1
    | exact certificate_sound 3 117 2 cell_3_117_2
    | exact certificate_sound 3 117 3 cell_3_117_3
    | exact certificate_sound 3 117 4 cell_3_117_4
    | exact certificate_sound 3 117 5 cell_3_117_5
theorem cell_3_118_0 : CertificateAt 3 118 0 := by decide +kernel
theorem cell_3_118_1 : CertificateAt 3 118 1 := by decide +kernel
theorem cell_3_118_2 : CertificateAt 3 118 2 := by decide +kernel
theorem cell_3_118_3 : CertificateAt 3 118 3 := by decide +kernel
theorem cell_3_118_4 : CertificateAt 3 118 4 := by decide +kernel
theorem cell_3_118_5 : CertificateAt 3 118 5 := by decide +kernel
theorem row_3_118 : ThresholdAt 3 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 118 0 cell_3_118_0
    | exact certificate_sound 3 118 1 cell_3_118_1
    | exact certificate_sound 3 118 2 cell_3_118_2
    | exact certificate_sound 3 118 3 cell_3_118_3
    | exact certificate_sound 3 118 4 cell_3_118_4
    | exact certificate_sound 3 118 5 cell_3_118_5
theorem cell_3_119_0 : CertificateAt 3 119 0 := by decide +kernel
theorem cell_3_119_1 : CertificateAt 3 119 1 := by decide +kernel
theorem cell_3_119_2 : CertificateAt 3 119 2 := by decide +kernel
theorem cell_3_119_3 : CertificateAt 3 119 3 := by decide +kernel
theorem cell_3_119_4 : CertificateAt 3 119 4 := by decide +kernel
theorem cell_3_119_5 : CertificateAt 3 119 5 := by decide +kernel
theorem row_3_119 : ThresholdAt 3 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 119 0 cell_3_119_0
    | exact certificate_sound 3 119 1 cell_3_119_1
    | exact certificate_sound 3 119 2 cell_3_119_2
    | exact certificate_sound 3 119 3 cell_3_119_3
    | exact certificate_sound 3 119 4 cell_3_119_4
    | exact certificate_sound 3 119 5 cell_3_119_5
theorem cell_3_120_0 : CertificateAt 3 120 0 := by decide +kernel
theorem cell_3_120_1 : CertificateAt 3 120 1 := by decide +kernel
theorem cell_3_120_2 : CertificateAt 3 120 2 := by decide +kernel
theorem cell_3_120_3 : CertificateAt 3 120 3 := by decide +kernel
theorem cell_3_120_4 : CertificateAt 3 120 4 := by decide +kernel
theorem cell_3_120_5 : CertificateAt 3 120 5 := by decide +kernel
theorem row_3_120 : ThresholdAt 3 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 120 0 cell_3_120_0
    | exact certificate_sound 3 120 1 cell_3_120_1
    | exact certificate_sound 3 120 2 cell_3_120_2
    | exact certificate_sound 3 120 3 cell_3_120_3
    | exact certificate_sound 3 120 4 cell_3_120_4
    | exact certificate_sound 3 120 5 cell_3_120_5
theorem cell_3_121_0 : CertificateAt 3 121 0 := by decide +kernel
theorem cell_3_121_1 : CertificateAt 3 121 1 := by decide +kernel
theorem cell_3_121_2 : CertificateAt 3 121 2 := by decide +kernel
theorem cell_3_121_3 : CertificateAt 3 121 3 := by decide +kernel
theorem cell_3_121_4 : CertificateAt 3 121 4 := by decide +kernel
theorem cell_3_121_5 : CertificateAt 3 121 5 := by decide +kernel
theorem row_3_121 : ThresholdAt 3 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 121 0 cell_3_121_0
    | exact certificate_sound 3 121 1 cell_3_121_1
    | exact certificate_sound 3 121 2 cell_3_121_2
    | exact certificate_sound 3 121 3 cell_3_121_3
    | exact certificate_sound 3 121 4 cell_3_121_4
    | exact certificate_sound 3 121 5 cell_3_121_5
theorem cell_3_122_0 : CertificateAt 3 122 0 := by decide +kernel
theorem cell_3_122_1 : CertificateAt 3 122 1 := by decide +kernel
theorem cell_3_122_2 : CertificateAt 3 122 2 := by decide +kernel
theorem cell_3_122_3 : CertificateAt 3 122 3 := by decide +kernel
theorem cell_3_122_4 : CertificateAt 3 122 4 := by decide +kernel
theorem cell_3_122_5 : CertificateAt 3 122 5 := by decide +kernel
theorem row_3_122 : ThresholdAt 3 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 122 0 cell_3_122_0
    | exact certificate_sound 3 122 1 cell_3_122_1
    | exact certificate_sound 3 122 2 cell_3_122_2
    | exact certificate_sound 3 122 3 cell_3_122_3
    | exact certificate_sound 3 122 4 cell_3_122_4
    | exact certificate_sound 3 122 5 cell_3_122_5
theorem cell_3_123_0 : CertificateAt 3 123 0 := by decide +kernel
theorem cell_3_123_1 : CertificateAt 3 123 1 := by decide +kernel
theorem cell_3_123_2 : CertificateAt 3 123 2 := by decide +kernel
theorem cell_3_123_3 : CertificateAt 3 123 3 := by decide +kernel
theorem cell_3_123_4 : CertificateAt 3 123 4 := by decide +kernel
theorem cell_3_123_5 : CertificateAt 3 123 5 := by decide +kernel
theorem row_3_123 : ThresholdAt 3 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 123 0 cell_3_123_0
    | exact certificate_sound 3 123 1 cell_3_123_1
    | exact certificate_sound 3 123 2 cell_3_123_2
    | exact certificate_sound 3 123 3 cell_3_123_3
    | exact certificate_sound 3 123 4 cell_3_123_4
    | exact certificate_sound 3 123 5 cell_3_123_5
theorem cell_3_124_0 : CertificateAt 3 124 0 := by decide +kernel
theorem cell_3_124_1 : CertificateAt 3 124 1 := by decide +kernel
theorem cell_3_124_2 : CertificateAt 3 124 2 := by decide +kernel
theorem cell_3_124_3 : CertificateAt 3 124 3 := by decide +kernel
theorem cell_3_124_4 : CertificateAt 3 124 4 := by decide +kernel
theorem cell_3_124_5 : CertificateAt 3 124 5 := by decide +kernel
theorem row_3_124 : ThresholdAt 3 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 124 0 cell_3_124_0
    | exact certificate_sound 3 124 1 cell_3_124_1
    | exact certificate_sound 3 124 2 cell_3_124_2
    | exact certificate_sound 3 124 3 cell_3_124_3
    | exact certificate_sound 3 124 4 cell_3_124_4
    | exact certificate_sound 3 124 5 cell_3_124_5
theorem cell_3_125_0 : CertificateAt 3 125 0 := by decide +kernel
theorem cell_3_125_1 : CertificateAt 3 125 1 := by decide +kernel
theorem cell_3_125_2 : CertificateAt 3 125 2 := by decide +kernel
theorem cell_3_125_3 : CertificateAt 3 125 3 := by decide +kernel
theorem cell_3_125_4 : CertificateAt 3 125 4 := by decide +kernel
theorem cell_3_125_5 : CertificateAt 3 125 5 := by decide +kernel
theorem row_3_125 : ThresholdAt 3 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 125 0 cell_3_125_0
    | exact certificate_sound 3 125 1 cell_3_125_1
    | exact certificate_sound 3 125 2 cell_3_125_2
    | exact certificate_sound 3 125 3 cell_3_125_3
    | exact certificate_sound 3 125 4 cell_3_125_4
    | exact certificate_sound 3 125 5 cell_3_125_5
theorem cell_3_126_0 : CertificateAt 3 126 0 := by decide +kernel
theorem cell_3_126_1 : CertificateAt 3 126 1 := by decide +kernel
theorem cell_3_126_2 : CertificateAt 3 126 2 := by decide +kernel
theorem cell_3_126_3 : CertificateAt 3 126 3 := by decide +kernel
theorem cell_3_126_4 : CertificateAt 3 126 4 := by decide +kernel
theorem cell_3_126_5 : CertificateAt 3 126 5 := by decide +kernel
theorem row_3_126 : ThresholdAt 3 126 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 126 0 cell_3_126_0
    | exact certificate_sound 3 126 1 cell_3_126_1
    | exact certificate_sound 3 126 2 cell_3_126_2
    | exact certificate_sound 3 126 3 cell_3_126_3
    | exact certificate_sound 3 126 4 cell_3_126_4
    | exact certificate_sound 3 126 5 cell_3_126_5
theorem cell_3_127_0 : CertificateAt 3 127 0 := by decide +kernel
theorem cell_3_127_1 : CertificateAt 3 127 1 := by decide +kernel
theorem cell_3_127_2 : CertificateAt 3 127 2 := by decide +kernel
theorem cell_3_127_3 : CertificateAt 3 127 3 := by decide +kernel
theorem cell_3_127_4 : CertificateAt 3 127 4 := by decide +kernel
theorem cell_3_127_5 : CertificateAt 3 127 5 := by decide +kernel
theorem row_3_127 : ThresholdAt 3 127 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 127 0 cell_3_127_0
    | exact certificate_sound 3 127 1 cell_3_127_1
    | exact certificate_sound 3 127 2 cell_3_127_2
    | exact certificate_sound 3 127 3 cell_3_127_3
    | exact certificate_sound 3 127 4 cell_3_127_4
    | exact certificate_sound 3 127 5 cell_3_127_5
theorem cell_3_128_0 : CertificateAt 3 128 0 := by decide +kernel
theorem cell_3_128_1 : CertificateAt 3 128 1 := by decide +kernel
theorem cell_3_128_2 : CertificateAt 3 128 2 := by decide +kernel
theorem cell_3_128_3 : CertificateAt 3 128 3 := by decide +kernel
theorem cell_3_128_4 : CertificateAt 3 128 4 := by decide +kernel
theorem cell_3_128_5 : CertificateAt 3 128 5 := by decide +kernel
theorem row_3_128 : ThresholdAt 3 128 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 128 0 cell_3_128_0
    | exact certificate_sound 3 128 1 cell_3_128_1
    | exact certificate_sound 3 128 2 cell_3_128_2
    | exact certificate_sound 3 128 3 cell_3_128_3
    | exact certificate_sound 3 128 4 cell_3_128_4
    | exact certificate_sound 3 128 5 cell_3_128_5
theorem cell_3_129_0 : CertificateAt 3 129 0 := by decide +kernel
theorem cell_3_129_1 : CertificateAt 3 129 1 := by decide +kernel
theorem cell_3_129_2 : CertificateAt 3 129 2 := by decide +kernel
theorem cell_3_129_3 : CertificateAt 3 129 3 := by decide +kernel
theorem cell_3_129_4 : CertificateAt 3 129 4 := by decide +kernel
theorem cell_3_129_5 : CertificateAt 3 129 5 := by decide +kernel
theorem row_3_129 : ThresholdAt 3 129 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 129 0 cell_3_129_0
    | exact certificate_sound 3 129 1 cell_3_129_1
    | exact certificate_sound 3 129 2 cell_3_129_2
    | exact certificate_sound 3 129 3 cell_3_129_3
    | exact certificate_sound 3 129 4 cell_3_129_4
    | exact certificate_sound 3 129 5 cell_3_129_5
theorem cell_3_130_0 : CertificateAt 3 130 0 := by decide +kernel
theorem cell_3_130_1 : CertificateAt 3 130 1 := by decide +kernel
theorem cell_3_130_2 : CertificateAt 3 130 2 := by decide +kernel
theorem cell_3_130_3 : CertificateAt 3 130 3 := by decide +kernel
theorem cell_3_130_4 : CertificateAt 3 130 4 := by decide +kernel
theorem cell_3_130_5 : CertificateAt 3 130 5 := by decide +kernel
theorem row_3_130 : ThresholdAt 3 130 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 130 0 cell_3_130_0
    | exact certificate_sound 3 130 1 cell_3_130_1
    | exact certificate_sound 3 130 2 cell_3_130_2
    | exact certificate_sound 3 130 3 cell_3_130_3
    | exact certificate_sound 3 130 4 cell_3_130_4
    | exact certificate_sound 3 130 5 cell_3_130_5
theorem cell_3_131_0 : CertificateAt 3 131 0 := by decide +kernel
theorem cell_3_131_1 : CertificateAt 3 131 1 := by decide +kernel
theorem cell_3_131_2 : CertificateAt 3 131 2 := by decide +kernel
theorem cell_3_131_3 : CertificateAt 3 131 3 := by decide +kernel
theorem cell_3_131_4 : CertificateAt 3 131 4 := by decide +kernel
theorem cell_3_131_5 : CertificateAt 3 131 5 := by decide +kernel
theorem row_3_131 : ThresholdAt 3 131 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 131 0 cell_3_131_0
    | exact certificate_sound 3 131 1 cell_3_131_1
    | exact certificate_sound 3 131 2 cell_3_131_2
    | exact certificate_sound 3 131 3 cell_3_131_3
    | exact certificate_sound 3 131 4 cell_3_131_4
    | exact certificate_sound 3 131 5 cell_3_131_5
theorem cell_3_132_0 : CertificateAt 3 132 0 := by decide +kernel
theorem cell_3_132_1 : CertificateAt 3 132 1 := by decide +kernel
theorem cell_3_132_2 : CertificateAt 3 132 2 := by decide +kernel
theorem cell_3_132_3 : CertificateAt 3 132 3 := by decide +kernel
theorem cell_3_132_4 : CertificateAt 3 132 4 := by decide +kernel
theorem cell_3_132_5 : CertificateAt 3 132 5 := by decide +kernel
theorem row_3_132 : ThresholdAt 3 132 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 132 0 cell_3_132_0
    | exact certificate_sound 3 132 1 cell_3_132_1
    | exact certificate_sound 3 132 2 cell_3_132_2
    | exact certificate_sound 3 132 3 cell_3_132_3
    | exact certificate_sound 3 132 4 cell_3_132_4
    | exact certificate_sound 3 132 5 cell_3_132_5
theorem cell_3_133_0 : CertificateAt 3 133 0 := by decide +kernel
theorem cell_3_133_1 : CertificateAt 3 133 1 := by decide +kernel
theorem cell_3_133_2 : CertificateAt 3 133 2 := by decide +kernel
theorem cell_3_133_3 : CertificateAt 3 133 3 := by decide +kernel
theorem cell_3_133_4 : CertificateAt 3 133 4 := by decide +kernel
theorem cell_3_133_5 : CertificateAt 3 133 5 := by decide +kernel
theorem row_3_133 : ThresholdAt 3 133 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 133 0 cell_3_133_0
    | exact certificate_sound 3 133 1 cell_3_133_1
    | exact certificate_sound 3 133 2 cell_3_133_2
    | exact certificate_sound 3 133 3 cell_3_133_3
    | exact certificate_sound 3 133 4 cell_3_133_4
    | exact certificate_sound 3 133 5 cell_3_133_5
theorem cell_3_134_0 : CertificateAt 3 134 0 := by decide +kernel
theorem cell_3_134_1 : CertificateAt 3 134 1 := by decide +kernel
theorem cell_3_134_2 : CertificateAt 3 134 2 := by decide +kernel
theorem cell_3_134_3 : CertificateAt 3 134 3 := by decide +kernel
theorem cell_3_134_4 : CertificateAt 3 134 4 := by decide +kernel
theorem cell_3_134_5 : CertificateAt 3 134 5 := by decide +kernel
theorem row_3_134 : ThresholdAt 3 134 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 134 0 cell_3_134_0
    | exact certificate_sound 3 134 1 cell_3_134_1
    | exact certificate_sound 3 134 2 cell_3_134_2
    | exact certificate_sound 3 134 3 cell_3_134_3
    | exact certificate_sound 3 134 4 cell_3_134_4
    | exact certificate_sound 3 134 5 cell_3_134_5
theorem cell_3_135_0 : CertificateAt 3 135 0 := by decide +kernel
theorem cell_3_135_1 : CertificateAt 3 135 1 := by decide +kernel
theorem cell_3_135_2 : CertificateAt 3 135 2 := by decide +kernel
theorem cell_3_135_3 : CertificateAt 3 135 3 := by decide +kernel
theorem cell_3_135_4 : CertificateAt 3 135 4 := by decide +kernel
theorem cell_3_135_5 : CertificateAt 3 135 5 := by decide +kernel
theorem row_3_135 : ThresholdAt 3 135 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 135 0 cell_3_135_0
    | exact certificate_sound 3 135 1 cell_3_135_1
    | exact certificate_sound 3 135 2 cell_3_135_2
    | exact certificate_sound 3 135 3 cell_3_135_3
    | exact certificate_sound 3 135 4 cell_3_135_4
    | exact certificate_sound 3 135 5 cell_3_135_5
theorem cell_3_136_0 : CertificateAt 3 136 0 := by decide +kernel
theorem cell_3_136_1 : CertificateAt 3 136 1 := by decide +kernel
theorem cell_3_136_2 : CertificateAt 3 136 2 := by decide +kernel
theorem cell_3_136_3 : CertificateAt 3 136 3 := by decide +kernel
theorem cell_3_136_4 : CertificateAt 3 136 4 := by decide +kernel
theorem cell_3_136_5 : CertificateAt 3 136 5 := by decide +kernel
theorem row_3_136 : ThresholdAt 3 136 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 3 136 0 cell_3_136_0
    | exact certificate_sound 3 136 1 cell_3_136_1
    | exact certificate_sound 3 136 2 cell_3_136_2
    | exact certificate_sound 3 136 3 cell_3_136_3
    | exact certificate_sound 3 136 4 cell_3_136_4
    | exact certificate_sound 3 136 5 cell_3_136_5
theorem checkedR3 : ∀ V ∈ List.range 137, ThresholdAt 3 V := by
  intro V hV
  have hv : V < 137 := List.mem_range.mp hV
  by_cases h0_137 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_3_0
              · have he : V = 1 := by omega
                subst V
                exact row_3_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_3_2
              · have he : V = 3 := by omega
                subst V
                exact row_3_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_3_4
              · have he : V = 5 := by omega
                subst V
                exact row_3_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_3_6
              · have he : V = 7 := by omega
                subst V
                exact row_3_7
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_3_8
              · have he : V = 9 := by omega
                subst V
                exact row_3_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_3_10
              · have he : V = 11 := by omega
                subst V
                exact row_3_11
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_3_12
              · have he : V = 13 := by omega
                subst V
                exact row_3_13
            · by_cases h14_17 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_3_14
              · by_cases h15_17 : V < 16
                · have he : V = 15 := by omega
                  subst V
                  exact row_3_15
                · have he : V = 16 := by omega
                  subst V
                  exact row_3_16
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_3_17
              · have he : V = 18 := by omega
                subst V
                exact row_3_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_3_19
              · have he : V = 20 := by omega
                subst V
                exact row_3_20
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_3_21
              · have he : V = 22 := by omega
                subst V
                exact row_3_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_3_23
              · have he : V = 24 := by omega
                subst V
                exact row_3_24
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_3_25
              · have he : V = 26 := by omega
                subst V
                exact row_3_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_3_27
              · have he : V = 28 := by omega
                subst V
                exact row_3_28
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_3_29
              · have he : V = 30 := by omega
                subst V
                exact row_3_30
            · by_cases h31_34 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_3_31
              · by_cases h32_34 : V < 33
                · have he : V = 32 := by omega
                  subst V
                  exact row_3_32
                · have he : V = 33 := by omega
                  subst V
                  exact row_3_33
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_3_34
              · have he : V = 35 := by omega
                subst V
                exact row_3_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_3_36
              · have he : V = 37 := by omega
                subst V
                exact row_3_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_3_38
              · have he : V = 39 := by omega
                subst V
                exact row_3_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_3_40
              · have he : V = 41 := by omega
                subst V
                exact row_3_41
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_3_42
              · have he : V = 43 := by omega
                subst V
                exact row_3_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_3_44
              · have he : V = 45 := by omega
                subst V
                exact row_3_45
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_3_46
              · have he : V = 47 := by omega
                subst V
                exact row_3_47
            · by_cases h48_51 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_3_48
              · by_cases h49_51 : V < 50
                · have he : V = 49 := by omega
                  subst V
                  exact row_3_49
                · have he : V = 50 := by omega
                  subst V
                  exact row_3_50
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_3_51
              · have he : V = 52 := by omega
                subst V
                exact row_3_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_3_53
              · have he : V = 54 := by omega
                subst V
                exact row_3_54
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_3_55
              · have he : V = 56 := by omega
                subst V
                exact row_3_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_3_57
              · have he : V = 58 := by omega
                subst V
                exact row_3_58
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_3_59
              · have he : V = 60 := by omega
                subst V
                exact row_3_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_3_61
              · have he : V = 62 := by omega
                subst V
                exact row_3_62
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_3_63
              · have he : V = 64 := by omega
                subst V
                exact row_3_64
            · by_cases h65_68 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_3_65
              · by_cases h66_68 : V < 67
                · have he : V = 66 := by omega
                  subst V
                  exact row_3_66
                · have he : V = 67 := by omega
                  subst V
                  exact row_3_67
  · by_cases h68_137 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_3_68
              · have he : V = 69 := by omega
                subst V
                exact row_3_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_3_70
              · have he : V = 71 := by omega
                subst V
                exact row_3_71
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_3_72
              · have he : V = 73 := by omega
                subst V
                exact row_3_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_3_74
              · have he : V = 75 := by omega
                subst V
                exact row_3_75
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_3_76
              · have he : V = 77 := by omega
                subst V
                exact row_3_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_3_78
              · have he : V = 79 := by omega
                subst V
                exact row_3_79
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_3_80
              · have he : V = 81 := by omega
                subst V
                exact row_3_81
            · by_cases h82_85 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_3_82
              · by_cases h83_85 : V < 84
                · have he : V = 83 := by omega
                  subst V
                  exact row_3_83
                · have he : V = 84 := by omega
                  subst V
                  exact row_3_84
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_3_85
              · have he : V = 86 := by omega
                subst V
                exact row_3_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_3_87
              · have he : V = 88 := by omega
                subst V
                exact row_3_88
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_3_89
              · have he : V = 90 := by omega
                subst V
                exact row_3_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_3_91
              · have he : V = 92 := by omega
                subst V
                exact row_3_92
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_3_93
              · have he : V = 94 := by omega
                subst V
                exact row_3_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_3_95
              · have he : V = 96 := by omega
                subst V
                exact row_3_96
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_3_97
              · have he : V = 98 := by omega
                subst V
                exact row_3_98
            · by_cases h99_102 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_3_99
              · by_cases h100_102 : V < 101
                · have he : V = 100 := by omega
                  subst V
                  exact row_3_100
                · have he : V = 101 := by omega
                  subst V
                  exact row_3_101
    · by_cases h102_137 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_3_102
              · have he : V = 103 := by omega
                subst V
                exact row_3_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_3_104
              · have he : V = 105 := by omega
                subst V
                exact row_3_105
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_3_106
              · have he : V = 107 := by omega
                subst V
                exact row_3_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_3_108
              · have he : V = 109 := by omega
                subst V
                exact row_3_109
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_3_110
              · have he : V = 111 := by omega
                subst V
                exact row_3_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_3_112
              · have he : V = 113 := by omega
                subst V
                exact row_3_113
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_3_114
              · have he : V = 115 := by omega
                subst V
                exact row_3_115
            · by_cases h116_119 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_3_116
              · by_cases h117_119 : V < 118
                · have he : V = 117 := by omega
                  subst V
                  exact row_3_117
                · have he : V = 118 := by omega
                  subst V
                  exact row_3_118
      · by_cases h119_137 : V < 128
        · by_cases h119_128 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_3_119
              · have he : V = 120 := by omega
                subst V
                exact row_3_120
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_3_121
              · have he : V = 122 := by omega
                subst V
                exact row_3_122
          · by_cases h123_128 : V < 125
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_3_123
              · have he : V = 124 := by omega
                subst V
                exact row_3_124
            · by_cases h125_128 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_3_125
              · by_cases h126_128 : V < 127
                · have he : V = 126 := by omega
                  subst V
                  exact row_3_126
                · have he : V = 127 := by omega
                  subst V
                  exact row_3_127
        · by_cases h128_137 : V < 132
          · by_cases h128_132 : V < 130
            · by_cases h128_130 : V < 129
              · have he : V = 128 := by omega
                subst V
                exact row_3_128
              · have he : V = 129 := by omega
                subst V
                exact row_3_129
            · by_cases h130_132 : V < 131
              · have he : V = 130 := by omega
                subst V
                exact row_3_130
              · have he : V = 131 := by omega
                subst V
                exact row_3_131
          · by_cases h132_137 : V < 134
            · by_cases h132_134 : V < 133
              · have he : V = 132 := by omega
                subst V
                exact row_3_132
              · have he : V = 133 := by omega
                subst V
                exact row_3_133
            · by_cases h134_137 : V < 135
              · have he : V = 134 := by omega
                subst V
                exact row_3_134
              · by_cases h135_137 : V < 136
                · have he : V = 135 := by omega
                  subst V
                  exact row_3_135
                · have he : V = 136 := by omega
                  subst V
                  exact row_3_136
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
