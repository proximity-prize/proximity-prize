import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked07

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_8_0_0 : CertificateAt 8 0 0 := by decide +kernel
theorem cell_8_0_1 : CertificateAt 8 0 1 := by decide +kernel
theorem cell_8_0_2 : CertificateAt 8 0 2 := by decide +kernel
theorem cell_8_0_3 : CertificateAt 8 0 3 := by decide +kernel
theorem cell_8_0_4 : CertificateAt 8 0 4 := by decide +kernel
theorem cell_8_0_5 : CertificateAt 8 0 5 := by decide +kernel
theorem row_8_0 : ThresholdAt 8 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 0 0 cell_8_0_0
    | exact certificate_sound 8 0 1 cell_8_0_1
    | exact certificate_sound 8 0 2 cell_8_0_2
    | exact certificate_sound 8 0 3 cell_8_0_3
    | exact certificate_sound 8 0 4 cell_8_0_4
    | exact certificate_sound 8 0 5 cell_8_0_5
theorem cell_8_1_0 : CertificateAt 8 1 0 := by decide +kernel
theorem cell_8_1_1 : CertificateAt 8 1 1 := by decide +kernel
theorem cell_8_1_2 : CertificateAt 8 1 2 := by decide +kernel
theorem cell_8_1_3 : CertificateAt 8 1 3 := by decide +kernel
theorem cell_8_1_4 : CertificateAt 8 1 4 := by decide +kernel
theorem cell_8_1_5 : CertificateAt 8 1 5 := by decide +kernel
theorem row_8_1 : ThresholdAt 8 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 1 0 cell_8_1_0
    | exact certificate_sound 8 1 1 cell_8_1_1
    | exact certificate_sound 8 1 2 cell_8_1_2
    | exact certificate_sound 8 1 3 cell_8_1_3
    | exact certificate_sound 8 1 4 cell_8_1_4
    | exact certificate_sound 8 1 5 cell_8_1_5
theorem cell_8_2_0 : CertificateAt 8 2 0 := by decide +kernel
theorem cell_8_2_1 : CertificateAt 8 2 1 := by decide +kernel
theorem cell_8_2_2 : CertificateAt 8 2 2 := by decide +kernel
theorem cell_8_2_3 : CertificateAt 8 2 3 := by decide +kernel
theorem cell_8_2_4 : CertificateAt 8 2 4 := by decide +kernel
theorem cell_8_2_5 : CertificateAt 8 2 5 := by decide +kernel
theorem row_8_2 : ThresholdAt 8 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 2 0 cell_8_2_0
    | exact certificate_sound 8 2 1 cell_8_2_1
    | exact certificate_sound 8 2 2 cell_8_2_2
    | exact certificate_sound 8 2 3 cell_8_2_3
    | exact certificate_sound 8 2 4 cell_8_2_4
    | exact certificate_sound 8 2 5 cell_8_2_5
theorem cell_8_3_0 : CertificateAt 8 3 0 := by decide +kernel
theorem cell_8_3_1 : CertificateAt 8 3 1 := by decide +kernel
theorem cell_8_3_2 : CertificateAt 8 3 2 := by decide +kernel
theorem cell_8_3_3 : CertificateAt 8 3 3 := by decide +kernel
theorem cell_8_3_4 : CertificateAt 8 3 4 := by decide +kernel
theorem cell_8_3_5 : CertificateAt 8 3 5 := by decide +kernel
theorem row_8_3 : ThresholdAt 8 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 3 0 cell_8_3_0
    | exact certificate_sound 8 3 1 cell_8_3_1
    | exact certificate_sound 8 3 2 cell_8_3_2
    | exact certificate_sound 8 3 3 cell_8_3_3
    | exact certificate_sound 8 3 4 cell_8_3_4
    | exact certificate_sound 8 3 5 cell_8_3_5
theorem cell_8_4_0 : CertificateAt 8 4 0 := by decide +kernel
theorem cell_8_4_1 : CertificateAt 8 4 1 := by decide +kernel
theorem cell_8_4_2 : CertificateAt 8 4 2 := by decide +kernel
theorem cell_8_4_3 : CertificateAt 8 4 3 := by decide +kernel
theorem cell_8_4_4 : CertificateAt 8 4 4 := by decide +kernel
theorem cell_8_4_5 : CertificateAt 8 4 5 := by decide +kernel
theorem row_8_4 : ThresholdAt 8 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 4 0 cell_8_4_0
    | exact certificate_sound 8 4 1 cell_8_4_1
    | exact certificate_sound 8 4 2 cell_8_4_2
    | exact certificate_sound 8 4 3 cell_8_4_3
    | exact certificate_sound 8 4 4 cell_8_4_4
    | exact certificate_sound 8 4 5 cell_8_4_5
theorem cell_8_5_0 : CertificateAt 8 5 0 := by decide +kernel
theorem cell_8_5_1 : CertificateAt 8 5 1 := by decide +kernel
theorem cell_8_5_2 : CertificateAt 8 5 2 := by decide +kernel
theorem cell_8_5_3 : CertificateAt 8 5 3 := by decide +kernel
theorem cell_8_5_4 : CertificateAt 8 5 4 := by decide +kernel
theorem cell_8_5_5 : CertificateAt 8 5 5 := by decide +kernel
theorem row_8_5 : ThresholdAt 8 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 5 0 cell_8_5_0
    | exact certificate_sound 8 5 1 cell_8_5_1
    | exact certificate_sound 8 5 2 cell_8_5_2
    | exact certificate_sound 8 5 3 cell_8_5_3
    | exact certificate_sound 8 5 4 cell_8_5_4
    | exact certificate_sound 8 5 5 cell_8_5_5
theorem cell_8_6_0 : CertificateAt 8 6 0 := by decide +kernel
theorem cell_8_6_1 : CertificateAt 8 6 1 := by decide +kernel
theorem cell_8_6_2 : CertificateAt 8 6 2 := by decide +kernel
theorem cell_8_6_3 : CertificateAt 8 6 3 := by decide +kernel
theorem cell_8_6_4 : CertificateAt 8 6 4 := by decide +kernel
theorem cell_8_6_5 : CertificateAt 8 6 5 := by decide +kernel
theorem row_8_6 : ThresholdAt 8 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 6 0 cell_8_6_0
    | exact certificate_sound 8 6 1 cell_8_6_1
    | exact certificate_sound 8 6 2 cell_8_6_2
    | exact certificate_sound 8 6 3 cell_8_6_3
    | exact certificate_sound 8 6 4 cell_8_6_4
    | exact certificate_sound 8 6 5 cell_8_6_5
theorem cell_8_7_0 : CertificateAt 8 7 0 := by decide +kernel
theorem cell_8_7_1 : CertificateAt 8 7 1 := by decide +kernel
theorem cell_8_7_2 : CertificateAt 8 7 2 := by decide +kernel
theorem cell_8_7_3 : CertificateAt 8 7 3 := by decide +kernel
theorem cell_8_7_4 : CertificateAt 8 7 4 := by decide +kernel
theorem cell_8_7_5 : CertificateAt 8 7 5 := by decide +kernel
theorem row_8_7 : ThresholdAt 8 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 7 0 cell_8_7_0
    | exact certificate_sound 8 7 1 cell_8_7_1
    | exact certificate_sound 8 7 2 cell_8_7_2
    | exact certificate_sound 8 7 3 cell_8_7_3
    | exact certificate_sound 8 7 4 cell_8_7_4
    | exact certificate_sound 8 7 5 cell_8_7_5
theorem cell_8_8_0 : CertificateAt 8 8 0 := by decide +kernel
theorem cell_8_8_1 : CertificateAt 8 8 1 := by decide +kernel
theorem cell_8_8_2 : CertificateAt 8 8 2 := by decide +kernel
theorem cell_8_8_3 : CertificateAt 8 8 3 := by decide +kernel
theorem cell_8_8_4 : CertificateAt 8 8 4 := by decide +kernel
theorem cell_8_8_5 : CertificateAt 8 8 5 := by decide +kernel
theorem row_8_8 : ThresholdAt 8 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 8 0 cell_8_8_0
    | exact certificate_sound 8 8 1 cell_8_8_1
    | exact certificate_sound 8 8 2 cell_8_8_2
    | exact certificate_sound 8 8 3 cell_8_8_3
    | exact certificate_sound 8 8 4 cell_8_8_4
    | exact certificate_sound 8 8 5 cell_8_8_5
theorem cell_8_9_0 : CertificateAt 8 9 0 := by decide +kernel
theorem cell_8_9_1 : CertificateAt 8 9 1 := by decide +kernel
theorem cell_8_9_2 : CertificateAt 8 9 2 := by decide +kernel
theorem cell_8_9_3 : CertificateAt 8 9 3 := by decide +kernel
theorem cell_8_9_4 : CertificateAt 8 9 4 := by decide +kernel
theorem cell_8_9_5 : CertificateAt 8 9 5 := by decide +kernel
theorem row_8_9 : ThresholdAt 8 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 9 0 cell_8_9_0
    | exact certificate_sound 8 9 1 cell_8_9_1
    | exact certificate_sound 8 9 2 cell_8_9_2
    | exact certificate_sound 8 9 3 cell_8_9_3
    | exact certificate_sound 8 9 4 cell_8_9_4
    | exact certificate_sound 8 9 5 cell_8_9_5
theorem cell_8_10_0 : CertificateAt 8 10 0 := by decide +kernel
theorem cell_8_10_1 : CertificateAt 8 10 1 := by decide +kernel
theorem cell_8_10_2 : CertificateAt 8 10 2 := by decide +kernel
theorem cell_8_10_3 : CertificateAt 8 10 3 := by decide +kernel
theorem cell_8_10_4 : CertificateAt 8 10 4 := by decide +kernel
theorem cell_8_10_5 : CertificateAt 8 10 5 := by decide +kernel
theorem row_8_10 : ThresholdAt 8 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 10 0 cell_8_10_0
    | exact certificate_sound 8 10 1 cell_8_10_1
    | exact certificate_sound 8 10 2 cell_8_10_2
    | exact certificate_sound 8 10 3 cell_8_10_3
    | exact certificate_sound 8 10 4 cell_8_10_4
    | exact certificate_sound 8 10 5 cell_8_10_5
theorem cell_8_11_0 : CertificateAt 8 11 0 := by decide +kernel
theorem cell_8_11_1 : CertificateAt 8 11 1 := by decide +kernel
theorem cell_8_11_2 : CertificateAt 8 11 2 := by decide +kernel
theorem cell_8_11_3 : CertificateAt 8 11 3 := by decide +kernel
theorem cell_8_11_4 : CertificateAt 8 11 4 := by decide +kernel
theorem cell_8_11_5 : CertificateAt 8 11 5 := by decide +kernel
theorem row_8_11 : ThresholdAt 8 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 11 0 cell_8_11_0
    | exact certificate_sound 8 11 1 cell_8_11_1
    | exact certificate_sound 8 11 2 cell_8_11_2
    | exact certificate_sound 8 11 3 cell_8_11_3
    | exact certificate_sound 8 11 4 cell_8_11_4
    | exact certificate_sound 8 11 5 cell_8_11_5
theorem cell_8_12_0 : CertificateAt 8 12 0 := by decide +kernel
theorem cell_8_12_1 : CertificateAt 8 12 1 := by decide +kernel
theorem cell_8_12_2 : CertificateAt 8 12 2 := by decide +kernel
theorem cell_8_12_3 : CertificateAt 8 12 3 := by decide +kernel
theorem cell_8_12_4 : CertificateAt 8 12 4 := by decide +kernel
theorem cell_8_12_5 : CertificateAt 8 12 5 := by decide +kernel
theorem row_8_12 : ThresholdAt 8 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 12 0 cell_8_12_0
    | exact certificate_sound 8 12 1 cell_8_12_1
    | exact certificate_sound 8 12 2 cell_8_12_2
    | exact certificate_sound 8 12 3 cell_8_12_3
    | exact certificate_sound 8 12 4 cell_8_12_4
    | exact certificate_sound 8 12 5 cell_8_12_5
theorem cell_8_13_0 : CertificateAt 8 13 0 := by decide +kernel
theorem cell_8_13_1 : CertificateAt 8 13 1 := by decide +kernel
theorem cell_8_13_2 : CertificateAt 8 13 2 := by decide +kernel
theorem cell_8_13_3 : CertificateAt 8 13 3 := by decide +kernel
theorem cell_8_13_4 : CertificateAt 8 13 4 := by decide +kernel
theorem cell_8_13_5 : CertificateAt 8 13 5 := by decide +kernel
theorem row_8_13 : ThresholdAt 8 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 13 0 cell_8_13_0
    | exact certificate_sound 8 13 1 cell_8_13_1
    | exact certificate_sound 8 13 2 cell_8_13_2
    | exact certificate_sound 8 13 3 cell_8_13_3
    | exact certificate_sound 8 13 4 cell_8_13_4
    | exact certificate_sound 8 13 5 cell_8_13_5
theorem cell_8_14_0 : CertificateAt 8 14 0 := by decide +kernel
theorem cell_8_14_1 : CertificateAt 8 14 1 := by decide +kernel
theorem cell_8_14_2 : CertificateAt 8 14 2 := by decide +kernel
theorem cell_8_14_3 : CertificateAt 8 14 3 := by decide +kernel
theorem cell_8_14_4 : CertificateAt 8 14 4 := by decide +kernel
theorem cell_8_14_5 : CertificateAt 8 14 5 := by decide +kernel
theorem row_8_14 : ThresholdAt 8 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 14 0 cell_8_14_0
    | exact certificate_sound 8 14 1 cell_8_14_1
    | exact certificate_sound 8 14 2 cell_8_14_2
    | exact certificate_sound 8 14 3 cell_8_14_3
    | exact certificate_sound 8 14 4 cell_8_14_4
    | exact certificate_sound 8 14 5 cell_8_14_5
theorem cell_8_15_0 : CertificateAt 8 15 0 := by decide +kernel
theorem cell_8_15_1 : CertificateAt 8 15 1 := by decide +kernel
theorem cell_8_15_2 : CertificateAt 8 15 2 := by decide +kernel
theorem cell_8_15_3 : CertificateAt 8 15 3 := by decide +kernel
theorem cell_8_15_4 : CertificateAt 8 15 4 := by decide +kernel
theorem cell_8_15_5 : CertificateAt 8 15 5 := by decide +kernel
theorem row_8_15 : ThresholdAt 8 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 15 0 cell_8_15_0
    | exact certificate_sound 8 15 1 cell_8_15_1
    | exact certificate_sound 8 15 2 cell_8_15_2
    | exact certificate_sound 8 15 3 cell_8_15_3
    | exact certificate_sound 8 15 4 cell_8_15_4
    | exact certificate_sound 8 15 5 cell_8_15_5
theorem cell_8_16_0 : CertificateAt 8 16 0 := by decide +kernel
theorem cell_8_16_1 : CertificateAt 8 16 1 := by decide +kernel
theorem cell_8_16_2 : CertificateAt 8 16 2 := by decide +kernel
theorem cell_8_16_3 : CertificateAt 8 16 3 := by decide +kernel
theorem cell_8_16_4 : CertificateAt 8 16 4 := by decide +kernel
theorem cell_8_16_5 : CertificateAt 8 16 5 := by decide +kernel
theorem row_8_16 : ThresholdAt 8 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 16 0 cell_8_16_0
    | exact certificate_sound 8 16 1 cell_8_16_1
    | exact certificate_sound 8 16 2 cell_8_16_2
    | exact certificate_sound 8 16 3 cell_8_16_3
    | exact certificate_sound 8 16 4 cell_8_16_4
    | exact certificate_sound 8 16 5 cell_8_16_5
theorem cell_8_17_0 : CertificateAt 8 17 0 := by decide +kernel
theorem cell_8_17_1 : CertificateAt 8 17 1 := by decide +kernel
theorem cell_8_17_2 : CertificateAt 8 17 2 := by decide +kernel
theorem cell_8_17_3 : CertificateAt 8 17 3 := by decide +kernel
theorem cell_8_17_4 : CertificateAt 8 17 4 := by decide +kernel
theorem cell_8_17_5 : CertificateAt 8 17 5 := by decide +kernel
theorem row_8_17 : ThresholdAt 8 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 17 0 cell_8_17_0
    | exact certificate_sound 8 17 1 cell_8_17_1
    | exact certificate_sound 8 17 2 cell_8_17_2
    | exact certificate_sound 8 17 3 cell_8_17_3
    | exact certificate_sound 8 17 4 cell_8_17_4
    | exact certificate_sound 8 17 5 cell_8_17_5
theorem cell_8_18_0 : CertificateAt 8 18 0 := by decide +kernel
theorem cell_8_18_1 : CertificateAt 8 18 1 := by decide +kernel
theorem cell_8_18_2 : CertificateAt 8 18 2 := by decide +kernel
theorem cell_8_18_3 : CertificateAt 8 18 3 := by decide +kernel
theorem cell_8_18_4 : CertificateAt 8 18 4 := by decide +kernel
theorem cell_8_18_5 : CertificateAt 8 18 5 := by decide +kernel
theorem row_8_18 : ThresholdAt 8 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 18 0 cell_8_18_0
    | exact certificate_sound 8 18 1 cell_8_18_1
    | exact certificate_sound 8 18 2 cell_8_18_2
    | exact certificate_sound 8 18 3 cell_8_18_3
    | exact certificate_sound 8 18 4 cell_8_18_4
    | exact certificate_sound 8 18 5 cell_8_18_5
theorem cell_8_19_0 : CertificateAt 8 19 0 := by decide +kernel
theorem cell_8_19_1 : CertificateAt 8 19 1 := by decide +kernel
theorem cell_8_19_2 : CertificateAt 8 19 2 := by decide +kernel
theorem cell_8_19_3 : CertificateAt 8 19 3 := by decide +kernel
theorem cell_8_19_4 : CertificateAt 8 19 4 := by decide +kernel
theorem cell_8_19_5 : CertificateAt 8 19 5 := by decide +kernel
theorem row_8_19 : ThresholdAt 8 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 19 0 cell_8_19_0
    | exact certificate_sound 8 19 1 cell_8_19_1
    | exact certificate_sound 8 19 2 cell_8_19_2
    | exact certificate_sound 8 19 3 cell_8_19_3
    | exact certificate_sound 8 19 4 cell_8_19_4
    | exact certificate_sound 8 19 5 cell_8_19_5
theorem cell_8_20_0 : CertificateAt 8 20 0 := by decide +kernel
theorem cell_8_20_1 : CertificateAt 8 20 1 := by decide +kernel
theorem cell_8_20_2 : CertificateAt 8 20 2 := by decide +kernel
theorem cell_8_20_3 : CertificateAt 8 20 3 := by decide +kernel
theorem cell_8_20_4 : CertificateAt 8 20 4 := by decide +kernel
theorem cell_8_20_5 : CertificateAt 8 20 5 := by decide +kernel
theorem row_8_20 : ThresholdAt 8 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 20 0 cell_8_20_0
    | exact certificate_sound 8 20 1 cell_8_20_1
    | exact certificate_sound 8 20 2 cell_8_20_2
    | exact certificate_sound 8 20 3 cell_8_20_3
    | exact certificate_sound 8 20 4 cell_8_20_4
    | exact certificate_sound 8 20 5 cell_8_20_5
theorem cell_8_21_0 : CertificateAt 8 21 0 := by decide +kernel
theorem cell_8_21_1 : CertificateAt 8 21 1 := by decide +kernel
theorem cell_8_21_2 : CertificateAt 8 21 2 := by decide +kernel
theorem cell_8_21_3 : CertificateAt 8 21 3 := by decide +kernel
theorem cell_8_21_4 : CertificateAt 8 21 4 := by decide +kernel
theorem cell_8_21_5 : CertificateAt 8 21 5 := by decide +kernel
theorem row_8_21 : ThresholdAt 8 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 21 0 cell_8_21_0
    | exact certificate_sound 8 21 1 cell_8_21_1
    | exact certificate_sound 8 21 2 cell_8_21_2
    | exact certificate_sound 8 21 3 cell_8_21_3
    | exact certificate_sound 8 21 4 cell_8_21_4
    | exact certificate_sound 8 21 5 cell_8_21_5
theorem cell_8_22_0 : CertificateAt 8 22 0 := by decide +kernel
theorem cell_8_22_1 : CertificateAt 8 22 1 := by decide +kernel
theorem cell_8_22_2 : CertificateAt 8 22 2 := by decide +kernel
theorem cell_8_22_3 : CertificateAt 8 22 3 := by decide +kernel
theorem cell_8_22_4 : CertificateAt 8 22 4 := by decide +kernel
theorem cell_8_22_5 : CertificateAt 8 22 5 := by decide +kernel
theorem row_8_22 : ThresholdAt 8 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 22 0 cell_8_22_0
    | exact certificate_sound 8 22 1 cell_8_22_1
    | exact certificate_sound 8 22 2 cell_8_22_2
    | exact certificate_sound 8 22 3 cell_8_22_3
    | exact certificate_sound 8 22 4 cell_8_22_4
    | exact certificate_sound 8 22 5 cell_8_22_5
theorem cell_8_23_0 : CertificateAt 8 23 0 := by decide +kernel
theorem cell_8_23_1 : CertificateAt 8 23 1 := by decide +kernel
theorem cell_8_23_2 : CertificateAt 8 23 2 := by decide +kernel
theorem cell_8_23_3 : CertificateAt 8 23 3 := by decide +kernel
theorem cell_8_23_4 : CertificateAt 8 23 4 := by decide +kernel
theorem cell_8_23_5 : CertificateAt 8 23 5 := by decide +kernel
theorem row_8_23 : ThresholdAt 8 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 23 0 cell_8_23_0
    | exact certificate_sound 8 23 1 cell_8_23_1
    | exact certificate_sound 8 23 2 cell_8_23_2
    | exact certificate_sound 8 23 3 cell_8_23_3
    | exact certificate_sound 8 23 4 cell_8_23_4
    | exact certificate_sound 8 23 5 cell_8_23_5
theorem cell_8_24_0 : CertificateAt 8 24 0 := by decide +kernel
theorem cell_8_24_1 : CertificateAt 8 24 1 := by decide +kernel
theorem cell_8_24_2 : CertificateAt 8 24 2 := by decide +kernel
theorem cell_8_24_3 : CertificateAt 8 24 3 := by decide +kernel
theorem cell_8_24_4 : CertificateAt 8 24 4 := by decide +kernel
theorem cell_8_24_5 : CertificateAt 8 24 5 := by decide +kernel
theorem row_8_24 : ThresholdAt 8 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 24 0 cell_8_24_0
    | exact certificate_sound 8 24 1 cell_8_24_1
    | exact certificate_sound 8 24 2 cell_8_24_2
    | exact certificate_sound 8 24 3 cell_8_24_3
    | exact certificate_sound 8 24 4 cell_8_24_4
    | exact certificate_sound 8 24 5 cell_8_24_5
theorem cell_8_25_0 : CertificateAt 8 25 0 := by decide +kernel
theorem cell_8_25_1 : CertificateAt 8 25 1 := by decide +kernel
theorem cell_8_25_2 : CertificateAt 8 25 2 := by decide +kernel
theorem cell_8_25_3 : CertificateAt 8 25 3 := by decide +kernel
theorem cell_8_25_4 : CertificateAt 8 25 4 := by decide +kernel
theorem cell_8_25_5 : CertificateAt 8 25 5 := by decide +kernel
theorem row_8_25 : ThresholdAt 8 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 25 0 cell_8_25_0
    | exact certificate_sound 8 25 1 cell_8_25_1
    | exact certificate_sound 8 25 2 cell_8_25_2
    | exact certificate_sound 8 25 3 cell_8_25_3
    | exact certificate_sound 8 25 4 cell_8_25_4
    | exact certificate_sound 8 25 5 cell_8_25_5
theorem cell_8_26_0 : CertificateAt 8 26 0 := by decide +kernel
theorem cell_8_26_1 : CertificateAt 8 26 1 := by decide +kernel
theorem cell_8_26_2 : CertificateAt 8 26 2 := by decide +kernel
theorem cell_8_26_3 : CertificateAt 8 26 3 := by decide +kernel
theorem cell_8_26_4 : CertificateAt 8 26 4 := by decide +kernel
theorem cell_8_26_5 : CertificateAt 8 26 5 := by decide +kernel
theorem row_8_26 : ThresholdAt 8 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 26 0 cell_8_26_0
    | exact certificate_sound 8 26 1 cell_8_26_1
    | exact certificate_sound 8 26 2 cell_8_26_2
    | exact certificate_sound 8 26 3 cell_8_26_3
    | exact certificate_sound 8 26 4 cell_8_26_4
    | exact certificate_sound 8 26 5 cell_8_26_5
theorem cell_8_27_0 : CertificateAt 8 27 0 := by decide +kernel
theorem cell_8_27_1 : CertificateAt 8 27 1 := by decide +kernel
theorem cell_8_27_2 : CertificateAt 8 27 2 := by decide +kernel
theorem cell_8_27_3 : CertificateAt 8 27 3 := by decide +kernel
theorem cell_8_27_4 : CertificateAt 8 27 4 := by decide +kernel
theorem cell_8_27_5 : CertificateAt 8 27 5 := by decide +kernel
theorem row_8_27 : ThresholdAt 8 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 27 0 cell_8_27_0
    | exact certificate_sound 8 27 1 cell_8_27_1
    | exact certificate_sound 8 27 2 cell_8_27_2
    | exact certificate_sound 8 27 3 cell_8_27_3
    | exact certificate_sound 8 27 4 cell_8_27_4
    | exact certificate_sound 8 27 5 cell_8_27_5
theorem cell_8_28_0 : CertificateAt 8 28 0 := by decide +kernel
theorem cell_8_28_1 : CertificateAt 8 28 1 := by decide +kernel
theorem cell_8_28_2 : CertificateAt 8 28 2 := by decide +kernel
theorem cell_8_28_3 : CertificateAt 8 28 3 := by decide +kernel
theorem cell_8_28_4 : CertificateAt 8 28 4 := by decide +kernel
theorem cell_8_28_5 : CertificateAt 8 28 5 := by decide +kernel
theorem row_8_28 : ThresholdAt 8 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 28 0 cell_8_28_0
    | exact certificate_sound 8 28 1 cell_8_28_1
    | exact certificate_sound 8 28 2 cell_8_28_2
    | exact certificate_sound 8 28 3 cell_8_28_3
    | exact certificate_sound 8 28 4 cell_8_28_4
    | exact certificate_sound 8 28 5 cell_8_28_5
theorem cell_8_29_0 : CertificateAt 8 29 0 := by decide +kernel
theorem cell_8_29_1 : CertificateAt 8 29 1 := by decide +kernel
theorem cell_8_29_2 : CertificateAt 8 29 2 := by decide +kernel
theorem cell_8_29_3 : CertificateAt 8 29 3 := by decide +kernel
theorem cell_8_29_4 : CertificateAt 8 29 4 := by decide +kernel
theorem cell_8_29_5 : CertificateAt 8 29 5 := by decide +kernel
theorem row_8_29 : ThresholdAt 8 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 29 0 cell_8_29_0
    | exact certificate_sound 8 29 1 cell_8_29_1
    | exact certificate_sound 8 29 2 cell_8_29_2
    | exact certificate_sound 8 29 3 cell_8_29_3
    | exact certificate_sound 8 29 4 cell_8_29_4
    | exact certificate_sound 8 29 5 cell_8_29_5
theorem cell_8_30_0 : CertificateAt 8 30 0 := by decide +kernel
theorem cell_8_30_1 : CertificateAt 8 30 1 := by decide +kernel
theorem cell_8_30_2 : CertificateAt 8 30 2 := by decide +kernel
theorem cell_8_30_3 : CertificateAt 8 30 3 := by decide +kernel
theorem cell_8_30_4 : CertificateAt 8 30 4 := by decide +kernel
theorem cell_8_30_5 : CertificateAt 8 30 5 := by decide +kernel
theorem row_8_30 : ThresholdAt 8 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 30 0 cell_8_30_0
    | exact certificate_sound 8 30 1 cell_8_30_1
    | exact certificate_sound 8 30 2 cell_8_30_2
    | exact certificate_sound 8 30 3 cell_8_30_3
    | exact certificate_sound 8 30 4 cell_8_30_4
    | exact certificate_sound 8 30 5 cell_8_30_5
theorem cell_8_31_0 : CertificateAt 8 31 0 := by decide +kernel
theorem cell_8_31_1 : CertificateAt 8 31 1 := by decide +kernel
theorem cell_8_31_2 : CertificateAt 8 31 2 := by decide +kernel
theorem cell_8_31_3 : CertificateAt 8 31 3 := by decide +kernel
theorem cell_8_31_4 : CertificateAt 8 31 4 := by decide +kernel
theorem cell_8_31_5 : CertificateAt 8 31 5 := by decide +kernel
theorem row_8_31 : ThresholdAt 8 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 31 0 cell_8_31_0
    | exact certificate_sound 8 31 1 cell_8_31_1
    | exact certificate_sound 8 31 2 cell_8_31_2
    | exact certificate_sound 8 31 3 cell_8_31_3
    | exact certificate_sound 8 31 4 cell_8_31_4
    | exact certificate_sound 8 31 5 cell_8_31_5
theorem cell_8_32_0 : CertificateAt 8 32 0 := by decide +kernel
theorem cell_8_32_1 : CertificateAt 8 32 1 := by decide +kernel
theorem cell_8_32_2 : CertificateAt 8 32 2 := by decide +kernel
theorem cell_8_32_3 : CertificateAt 8 32 3 := by decide +kernel
theorem cell_8_32_4 : CertificateAt 8 32 4 := by decide +kernel
theorem cell_8_32_5 : CertificateAt 8 32 5 := by decide +kernel
theorem row_8_32 : ThresholdAt 8 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 32 0 cell_8_32_0
    | exact certificate_sound 8 32 1 cell_8_32_1
    | exact certificate_sound 8 32 2 cell_8_32_2
    | exact certificate_sound 8 32 3 cell_8_32_3
    | exact certificate_sound 8 32 4 cell_8_32_4
    | exact certificate_sound 8 32 5 cell_8_32_5
theorem cell_8_33_0 : CertificateAt 8 33 0 := by decide +kernel
theorem cell_8_33_1 : CertificateAt 8 33 1 := by decide +kernel
theorem cell_8_33_2 : CertificateAt 8 33 2 := by decide +kernel
theorem cell_8_33_3 : CertificateAt 8 33 3 := by decide +kernel
theorem cell_8_33_4 : CertificateAt 8 33 4 := by decide +kernel
theorem cell_8_33_5 : CertificateAt 8 33 5 := by decide +kernel
theorem row_8_33 : ThresholdAt 8 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 33 0 cell_8_33_0
    | exact certificate_sound 8 33 1 cell_8_33_1
    | exact certificate_sound 8 33 2 cell_8_33_2
    | exact certificate_sound 8 33 3 cell_8_33_3
    | exact certificate_sound 8 33 4 cell_8_33_4
    | exact certificate_sound 8 33 5 cell_8_33_5
theorem cell_8_34_0 : CertificateAt 8 34 0 := by decide +kernel
theorem cell_8_34_1 : CertificateAt 8 34 1 := by decide +kernel
theorem cell_8_34_2 : CertificateAt 8 34 2 := by decide +kernel
theorem cell_8_34_3 : CertificateAt 8 34 3 := by decide +kernel
theorem cell_8_34_4 : CertificateAt 8 34 4 := by decide +kernel
theorem cell_8_34_5 : CertificateAt 8 34 5 := by decide +kernel
theorem row_8_34 : ThresholdAt 8 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 34 0 cell_8_34_0
    | exact certificate_sound 8 34 1 cell_8_34_1
    | exact certificate_sound 8 34 2 cell_8_34_2
    | exact certificate_sound 8 34 3 cell_8_34_3
    | exact certificate_sound 8 34 4 cell_8_34_4
    | exact certificate_sound 8 34 5 cell_8_34_5
theorem cell_8_35_0 : CertificateAt 8 35 0 := by decide +kernel
theorem cell_8_35_1 : CertificateAt 8 35 1 := by decide +kernel
theorem cell_8_35_2 : CertificateAt 8 35 2 := by decide +kernel
theorem cell_8_35_3 : CertificateAt 8 35 3 := by decide +kernel
theorem cell_8_35_4 : CertificateAt 8 35 4 := by decide +kernel
theorem cell_8_35_5 : CertificateAt 8 35 5 := by decide +kernel
theorem row_8_35 : ThresholdAt 8 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 35 0 cell_8_35_0
    | exact certificate_sound 8 35 1 cell_8_35_1
    | exact certificate_sound 8 35 2 cell_8_35_2
    | exact certificate_sound 8 35 3 cell_8_35_3
    | exact certificate_sound 8 35 4 cell_8_35_4
    | exact certificate_sound 8 35 5 cell_8_35_5
theorem cell_8_36_0 : CertificateAt 8 36 0 := by decide +kernel
theorem cell_8_36_1 : CertificateAt 8 36 1 := by decide +kernel
theorem cell_8_36_2 : CertificateAt 8 36 2 := by decide +kernel
theorem cell_8_36_3 : CertificateAt 8 36 3 := by decide +kernel
theorem cell_8_36_4 : CertificateAt 8 36 4 := by decide +kernel
theorem cell_8_36_5 : CertificateAt 8 36 5 := by decide +kernel
theorem row_8_36 : ThresholdAt 8 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 36 0 cell_8_36_0
    | exact certificate_sound 8 36 1 cell_8_36_1
    | exact certificate_sound 8 36 2 cell_8_36_2
    | exact certificate_sound 8 36 3 cell_8_36_3
    | exact certificate_sound 8 36 4 cell_8_36_4
    | exact certificate_sound 8 36 5 cell_8_36_5
theorem cell_8_37_0 : CertificateAt 8 37 0 := by decide +kernel
theorem cell_8_37_1 : CertificateAt 8 37 1 := by decide +kernel
theorem cell_8_37_2 : CertificateAt 8 37 2 := by decide +kernel
theorem cell_8_37_3 : CertificateAt 8 37 3 := by decide +kernel
theorem cell_8_37_4 : CertificateAt 8 37 4 := by decide +kernel
theorem cell_8_37_5 : CertificateAt 8 37 5 := by decide +kernel
theorem row_8_37 : ThresholdAt 8 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 37 0 cell_8_37_0
    | exact certificate_sound 8 37 1 cell_8_37_1
    | exact certificate_sound 8 37 2 cell_8_37_2
    | exact certificate_sound 8 37 3 cell_8_37_3
    | exact certificate_sound 8 37 4 cell_8_37_4
    | exact certificate_sound 8 37 5 cell_8_37_5
theorem cell_8_38_0 : CertificateAt 8 38 0 := by decide +kernel
theorem cell_8_38_1 : CertificateAt 8 38 1 := by decide +kernel
theorem cell_8_38_2 : CertificateAt 8 38 2 := by decide +kernel
theorem cell_8_38_3 : CertificateAt 8 38 3 := by decide +kernel
theorem cell_8_38_4 : CertificateAt 8 38 4 := by decide +kernel
theorem cell_8_38_5 : CertificateAt 8 38 5 := by decide +kernel
theorem row_8_38 : ThresholdAt 8 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 38 0 cell_8_38_0
    | exact certificate_sound 8 38 1 cell_8_38_1
    | exact certificate_sound 8 38 2 cell_8_38_2
    | exact certificate_sound 8 38 3 cell_8_38_3
    | exact certificate_sound 8 38 4 cell_8_38_4
    | exact certificate_sound 8 38 5 cell_8_38_5
theorem cell_8_39_0 : CertificateAt 8 39 0 := by decide +kernel
theorem cell_8_39_1 : CertificateAt 8 39 1 := by decide +kernel
theorem cell_8_39_2 : CertificateAt 8 39 2 := by decide +kernel
theorem cell_8_39_3 : CertificateAt 8 39 3 := by decide +kernel
theorem cell_8_39_4 : CertificateAt 8 39 4 := by decide +kernel
theorem cell_8_39_5 : CertificateAt 8 39 5 := by decide +kernel
theorem row_8_39 : ThresholdAt 8 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 39 0 cell_8_39_0
    | exact certificate_sound 8 39 1 cell_8_39_1
    | exact certificate_sound 8 39 2 cell_8_39_2
    | exact certificate_sound 8 39 3 cell_8_39_3
    | exact certificate_sound 8 39 4 cell_8_39_4
    | exact certificate_sound 8 39 5 cell_8_39_5
theorem cell_8_40_0 : CertificateAt 8 40 0 := by decide +kernel
theorem cell_8_40_1 : CertificateAt 8 40 1 := by decide +kernel
theorem cell_8_40_2 : CertificateAt 8 40 2 := by decide +kernel
theorem cell_8_40_3 : CertificateAt 8 40 3 := by decide +kernel
theorem cell_8_40_4 : CertificateAt 8 40 4 := by decide +kernel
theorem cell_8_40_5 : CertificateAt 8 40 5 := by decide +kernel
theorem row_8_40 : ThresholdAt 8 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 40 0 cell_8_40_0
    | exact certificate_sound 8 40 1 cell_8_40_1
    | exact certificate_sound 8 40 2 cell_8_40_2
    | exact certificate_sound 8 40 3 cell_8_40_3
    | exact certificate_sound 8 40 4 cell_8_40_4
    | exact certificate_sound 8 40 5 cell_8_40_5
theorem cell_8_41_0 : CertificateAt 8 41 0 := by decide +kernel
theorem cell_8_41_1 : CertificateAt 8 41 1 := by decide +kernel
theorem cell_8_41_2 : CertificateAt 8 41 2 := by decide +kernel
theorem cell_8_41_3 : CertificateAt 8 41 3 := by decide +kernel
theorem cell_8_41_4 : CertificateAt 8 41 4 := by decide +kernel
theorem cell_8_41_5 : CertificateAt 8 41 5 := by decide +kernel
theorem row_8_41 : ThresholdAt 8 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 41 0 cell_8_41_0
    | exact certificate_sound 8 41 1 cell_8_41_1
    | exact certificate_sound 8 41 2 cell_8_41_2
    | exact certificate_sound 8 41 3 cell_8_41_3
    | exact certificate_sound 8 41 4 cell_8_41_4
    | exact certificate_sound 8 41 5 cell_8_41_5
theorem cell_8_42_0 : CertificateAt 8 42 0 := by decide +kernel
theorem cell_8_42_1 : CertificateAt 8 42 1 := by decide +kernel
theorem cell_8_42_2 : CertificateAt 8 42 2 := by decide +kernel
theorem cell_8_42_3 : CertificateAt 8 42 3 := by decide +kernel
theorem cell_8_42_4 : CertificateAt 8 42 4 := by decide +kernel
theorem cell_8_42_5 : CertificateAt 8 42 5 := by decide +kernel
theorem row_8_42 : ThresholdAt 8 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 42 0 cell_8_42_0
    | exact certificate_sound 8 42 1 cell_8_42_1
    | exact certificate_sound 8 42 2 cell_8_42_2
    | exact certificate_sound 8 42 3 cell_8_42_3
    | exact certificate_sound 8 42 4 cell_8_42_4
    | exact certificate_sound 8 42 5 cell_8_42_5
theorem cell_8_43_0 : CertificateAt 8 43 0 := by decide +kernel
theorem cell_8_43_1 : CertificateAt 8 43 1 := by decide +kernel
theorem cell_8_43_2 : CertificateAt 8 43 2 := by decide +kernel
theorem cell_8_43_3 : CertificateAt 8 43 3 := by decide +kernel
theorem cell_8_43_4 : CertificateAt 8 43 4 := by decide +kernel
theorem cell_8_43_5 : CertificateAt 8 43 5 := by decide +kernel
theorem row_8_43 : ThresholdAt 8 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 43 0 cell_8_43_0
    | exact certificate_sound 8 43 1 cell_8_43_1
    | exact certificate_sound 8 43 2 cell_8_43_2
    | exact certificate_sound 8 43 3 cell_8_43_3
    | exact certificate_sound 8 43 4 cell_8_43_4
    | exact certificate_sound 8 43 5 cell_8_43_5
theorem cell_8_44_0 : CertificateAt 8 44 0 := by decide +kernel
theorem cell_8_44_1 : CertificateAt 8 44 1 := by decide +kernel
theorem cell_8_44_2 : CertificateAt 8 44 2 := by decide +kernel
theorem cell_8_44_3 : CertificateAt 8 44 3 := by decide +kernel
theorem cell_8_44_4 : CertificateAt 8 44 4 := by decide +kernel
theorem cell_8_44_5 : CertificateAt 8 44 5 := by decide +kernel
theorem row_8_44 : ThresholdAt 8 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 44 0 cell_8_44_0
    | exact certificate_sound 8 44 1 cell_8_44_1
    | exact certificate_sound 8 44 2 cell_8_44_2
    | exact certificate_sound 8 44 3 cell_8_44_3
    | exact certificate_sound 8 44 4 cell_8_44_4
    | exact certificate_sound 8 44 5 cell_8_44_5
theorem cell_8_45_0 : CertificateAt 8 45 0 := by decide +kernel
theorem cell_8_45_1 : CertificateAt 8 45 1 := by decide +kernel
theorem cell_8_45_2 : CertificateAt 8 45 2 := by decide +kernel
theorem cell_8_45_3 : CertificateAt 8 45 3 := by decide +kernel
theorem cell_8_45_4 : CertificateAt 8 45 4 := by decide +kernel
theorem cell_8_45_5 : CertificateAt 8 45 5 := by decide +kernel
theorem row_8_45 : ThresholdAt 8 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 45 0 cell_8_45_0
    | exact certificate_sound 8 45 1 cell_8_45_1
    | exact certificate_sound 8 45 2 cell_8_45_2
    | exact certificate_sound 8 45 3 cell_8_45_3
    | exact certificate_sound 8 45 4 cell_8_45_4
    | exact certificate_sound 8 45 5 cell_8_45_5
theorem cell_8_46_0 : CertificateAt 8 46 0 := by decide +kernel
theorem cell_8_46_1 : CertificateAt 8 46 1 := by decide +kernel
theorem cell_8_46_2 : CertificateAt 8 46 2 := by decide +kernel
theorem cell_8_46_3 : CertificateAt 8 46 3 := by decide +kernel
theorem cell_8_46_4 : CertificateAt 8 46 4 := by decide +kernel
theorem cell_8_46_5 : CertificateAt 8 46 5 := by decide +kernel
theorem row_8_46 : ThresholdAt 8 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 46 0 cell_8_46_0
    | exact certificate_sound 8 46 1 cell_8_46_1
    | exact certificate_sound 8 46 2 cell_8_46_2
    | exact certificate_sound 8 46 3 cell_8_46_3
    | exact certificate_sound 8 46 4 cell_8_46_4
    | exact certificate_sound 8 46 5 cell_8_46_5
theorem cell_8_47_0 : CertificateAt 8 47 0 := by decide +kernel
theorem cell_8_47_1 : CertificateAt 8 47 1 := by decide +kernel
theorem cell_8_47_2 : CertificateAt 8 47 2 := by decide +kernel
theorem cell_8_47_3 : CertificateAt 8 47 3 := by decide +kernel
theorem cell_8_47_4 : CertificateAt 8 47 4 := by decide +kernel
theorem cell_8_47_5 : CertificateAt 8 47 5 := by decide +kernel
theorem row_8_47 : ThresholdAt 8 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 47 0 cell_8_47_0
    | exact certificate_sound 8 47 1 cell_8_47_1
    | exact certificate_sound 8 47 2 cell_8_47_2
    | exact certificate_sound 8 47 3 cell_8_47_3
    | exact certificate_sound 8 47 4 cell_8_47_4
    | exact certificate_sound 8 47 5 cell_8_47_5
theorem cell_8_48_0 : CertificateAt 8 48 0 := by decide +kernel
theorem cell_8_48_1 : CertificateAt 8 48 1 := by decide +kernel
theorem cell_8_48_2 : CertificateAt 8 48 2 := by decide +kernel
theorem cell_8_48_3 : CertificateAt 8 48 3 := by decide +kernel
theorem cell_8_48_4 : CertificateAt 8 48 4 := by decide +kernel
theorem cell_8_48_5 : CertificateAt 8 48 5 := by decide +kernel
theorem row_8_48 : ThresholdAt 8 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 48 0 cell_8_48_0
    | exact certificate_sound 8 48 1 cell_8_48_1
    | exact certificate_sound 8 48 2 cell_8_48_2
    | exact certificate_sound 8 48 3 cell_8_48_3
    | exact certificate_sound 8 48 4 cell_8_48_4
    | exact certificate_sound 8 48 5 cell_8_48_5
theorem cell_8_49_0 : CertificateAt 8 49 0 := by decide +kernel
theorem cell_8_49_1 : CertificateAt 8 49 1 := by decide +kernel
theorem cell_8_49_2 : CertificateAt 8 49 2 := by decide +kernel
theorem cell_8_49_3 : CertificateAt 8 49 3 := by decide +kernel
theorem cell_8_49_4 : CertificateAt 8 49 4 := by decide +kernel
theorem cell_8_49_5 : CertificateAt 8 49 5 := by decide +kernel
theorem row_8_49 : ThresholdAt 8 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 49 0 cell_8_49_0
    | exact certificate_sound 8 49 1 cell_8_49_1
    | exact certificate_sound 8 49 2 cell_8_49_2
    | exact certificate_sound 8 49 3 cell_8_49_3
    | exact certificate_sound 8 49 4 cell_8_49_4
    | exact certificate_sound 8 49 5 cell_8_49_5
theorem cell_8_50_0 : CertificateAt 8 50 0 := by decide +kernel
theorem cell_8_50_1 : CertificateAt 8 50 1 := by decide +kernel
theorem cell_8_50_2 : CertificateAt 8 50 2 := by decide +kernel
theorem cell_8_50_3 : CertificateAt 8 50 3 := by decide +kernel
theorem cell_8_50_4 : CertificateAt 8 50 4 := by decide +kernel
theorem cell_8_50_5 : CertificateAt 8 50 5 := by decide +kernel
theorem row_8_50 : ThresholdAt 8 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 50 0 cell_8_50_0
    | exact certificate_sound 8 50 1 cell_8_50_1
    | exact certificate_sound 8 50 2 cell_8_50_2
    | exact certificate_sound 8 50 3 cell_8_50_3
    | exact certificate_sound 8 50 4 cell_8_50_4
    | exact certificate_sound 8 50 5 cell_8_50_5
theorem cell_8_51_0 : CertificateAt 8 51 0 := by decide +kernel
theorem cell_8_51_1 : CertificateAt 8 51 1 := by decide +kernel
theorem cell_8_51_2 : CertificateAt 8 51 2 := by decide +kernel
theorem cell_8_51_3 : CertificateAt 8 51 3 := by decide +kernel
theorem cell_8_51_4 : CertificateAt 8 51 4 := by decide +kernel
theorem cell_8_51_5 : CertificateAt 8 51 5 := by decide +kernel
theorem row_8_51 : ThresholdAt 8 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 51 0 cell_8_51_0
    | exact certificate_sound 8 51 1 cell_8_51_1
    | exact certificate_sound 8 51 2 cell_8_51_2
    | exact certificate_sound 8 51 3 cell_8_51_3
    | exact certificate_sound 8 51 4 cell_8_51_4
    | exact certificate_sound 8 51 5 cell_8_51_5
theorem cell_8_52_0 : CertificateAt 8 52 0 := by decide +kernel
theorem cell_8_52_1 : CertificateAt 8 52 1 := by decide +kernel
theorem cell_8_52_2 : CertificateAt 8 52 2 := by decide +kernel
theorem cell_8_52_3 : CertificateAt 8 52 3 := by decide +kernel
theorem cell_8_52_4 : CertificateAt 8 52 4 := by decide +kernel
theorem cell_8_52_5 : CertificateAt 8 52 5 := by decide +kernel
theorem row_8_52 : ThresholdAt 8 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 52 0 cell_8_52_0
    | exact certificate_sound 8 52 1 cell_8_52_1
    | exact certificate_sound 8 52 2 cell_8_52_2
    | exact certificate_sound 8 52 3 cell_8_52_3
    | exact certificate_sound 8 52 4 cell_8_52_4
    | exact certificate_sound 8 52 5 cell_8_52_5
theorem cell_8_53_0 : CertificateAt 8 53 0 := by decide +kernel
theorem cell_8_53_1 : CertificateAt 8 53 1 := by decide +kernel
theorem cell_8_53_2 : CertificateAt 8 53 2 := by decide +kernel
theorem cell_8_53_3 : CertificateAt 8 53 3 := by decide +kernel
theorem cell_8_53_4 : CertificateAt 8 53 4 := by decide +kernel
theorem cell_8_53_5 : CertificateAt 8 53 5 := by decide +kernel
theorem row_8_53 : ThresholdAt 8 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 53 0 cell_8_53_0
    | exact certificate_sound 8 53 1 cell_8_53_1
    | exact certificate_sound 8 53 2 cell_8_53_2
    | exact certificate_sound 8 53 3 cell_8_53_3
    | exact certificate_sound 8 53 4 cell_8_53_4
    | exact certificate_sound 8 53 5 cell_8_53_5
theorem cell_8_54_0 : CertificateAt 8 54 0 := by decide +kernel
theorem cell_8_54_1 : CertificateAt 8 54 1 := by decide +kernel
theorem cell_8_54_2 : CertificateAt 8 54 2 := by decide +kernel
theorem cell_8_54_3 : CertificateAt 8 54 3 := by decide +kernel
theorem cell_8_54_4 : CertificateAt 8 54 4 := by decide +kernel
theorem cell_8_54_5 : CertificateAt 8 54 5 := by decide +kernel
theorem row_8_54 : ThresholdAt 8 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 54 0 cell_8_54_0
    | exact certificate_sound 8 54 1 cell_8_54_1
    | exact certificate_sound 8 54 2 cell_8_54_2
    | exact certificate_sound 8 54 3 cell_8_54_3
    | exact certificate_sound 8 54 4 cell_8_54_4
    | exact certificate_sound 8 54 5 cell_8_54_5
theorem cell_8_55_0 : CertificateAt 8 55 0 := by decide +kernel
theorem cell_8_55_1 : CertificateAt 8 55 1 := by decide +kernel
theorem cell_8_55_2 : CertificateAt 8 55 2 := by decide +kernel
theorem cell_8_55_3 : CertificateAt 8 55 3 := by decide +kernel
theorem cell_8_55_4 : CertificateAt 8 55 4 := by decide +kernel
theorem cell_8_55_5 : CertificateAt 8 55 5 := by decide +kernel
theorem row_8_55 : ThresholdAt 8 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 55 0 cell_8_55_0
    | exact certificate_sound 8 55 1 cell_8_55_1
    | exact certificate_sound 8 55 2 cell_8_55_2
    | exact certificate_sound 8 55 3 cell_8_55_3
    | exact certificate_sound 8 55 4 cell_8_55_4
    | exact certificate_sound 8 55 5 cell_8_55_5
theorem cell_8_56_0 : CertificateAt 8 56 0 := by decide +kernel
theorem cell_8_56_1 : CertificateAt 8 56 1 := by decide +kernel
theorem cell_8_56_2 : CertificateAt 8 56 2 := by decide +kernel
theorem cell_8_56_3 : CertificateAt 8 56 3 := by decide +kernel
theorem cell_8_56_4 : CertificateAt 8 56 4 := by decide +kernel
theorem cell_8_56_5 : CertificateAt 8 56 5 := by decide +kernel
theorem row_8_56 : ThresholdAt 8 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 56 0 cell_8_56_0
    | exact certificate_sound 8 56 1 cell_8_56_1
    | exact certificate_sound 8 56 2 cell_8_56_2
    | exact certificate_sound 8 56 3 cell_8_56_3
    | exact certificate_sound 8 56 4 cell_8_56_4
    | exact certificate_sound 8 56 5 cell_8_56_5
theorem cell_8_57_0 : CertificateAt 8 57 0 := by decide +kernel
theorem cell_8_57_1 : CertificateAt 8 57 1 := by decide +kernel
theorem cell_8_57_2 : CertificateAt 8 57 2 := by decide +kernel
theorem cell_8_57_3 : CertificateAt 8 57 3 := by decide +kernel
theorem cell_8_57_4 : CertificateAt 8 57 4 := by decide +kernel
theorem cell_8_57_5 : CertificateAt 8 57 5 := by decide +kernel
theorem row_8_57 : ThresholdAt 8 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 57 0 cell_8_57_0
    | exact certificate_sound 8 57 1 cell_8_57_1
    | exact certificate_sound 8 57 2 cell_8_57_2
    | exact certificate_sound 8 57 3 cell_8_57_3
    | exact certificate_sound 8 57 4 cell_8_57_4
    | exact certificate_sound 8 57 5 cell_8_57_5
theorem cell_8_58_0 : CertificateAt 8 58 0 := by decide +kernel
theorem cell_8_58_1 : CertificateAt 8 58 1 := by decide +kernel
theorem cell_8_58_2 : CertificateAt 8 58 2 := by decide +kernel
theorem cell_8_58_3 : CertificateAt 8 58 3 := by decide +kernel
theorem cell_8_58_4 : CertificateAt 8 58 4 := by decide +kernel
theorem cell_8_58_5 : CertificateAt 8 58 5 := by decide +kernel
theorem row_8_58 : ThresholdAt 8 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 58 0 cell_8_58_0
    | exact certificate_sound 8 58 1 cell_8_58_1
    | exact certificate_sound 8 58 2 cell_8_58_2
    | exact certificate_sound 8 58 3 cell_8_58_3
    | exact certificate_sound 8 58 4 cell_8_58_4
    | exact certificate_sound 8 58 5 cell_8_58_5
theorem cell_8_59_0 : CertificateAt 8 59 0 := by decide +kernel
theorem cell_8_59_1 : CertificateAt 8 59 1 := by decide +kernel
theorem cell_8_59_2 : CertificateAt 8 59 2 := by decide +kernel
theorem cell_8_59_3 : CertificateAt 8 59 3 := by decide +kernel
theorem cell_8_59_4 : CertificateAt 8 59 4 := by decide +kernel
theorem cell_8_59_5 : CertificateAt 8 59 5 := by decide +kernel
theorem row_8_59 : ThresholdAt 8 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 59 0 cell_8_59_0
    | exact certificate_sound 8 59 1 cell_8_59_1
    | exact certificate_sound 8 59 2 cell_8_59_2
    | exact certificate_sound 8 59 3 cell_8_59_3
    | exact certificate_sound 8 59 4 cell_8_59_4
    | exact certificate_sound 8 59 5 cell_8_59_5
theorem cell_8_60_0 : CertificateAt 8 60 0 := by decide +kernel
theorem cell_8_60_1 : CertificateAt 8 60 1 := by decide +kernel
theorem cell_8_60_2 : CertificateAt 8 60 2 := by decide +kernel
theorem cell_8_60_3 : CertificateAt 8 60 3 := by decide +kernel
theorem cell_8_60_4 : CertificateAt 8 60 4 := by decide +kernel
theorem cell_8_60_5 : CertificateAt 8 60 5 := by decide +kernel
theorem row_8_60 : ThresholdAt 8 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 60 0 cell_8_60_0
    | exact certificate_sound 8 60 1 cell_8_60_1
    | exact certificate_sound 8 60 2 cell_8_60_2
    | exact certificate_sound 8 60 3 cell_8_60_3
    | exact certificate_sound 8 60 4 cell_8_60_4
    | exact certificate_sound 8 60 5 cell_8_60_5
theorem cell_8_61_0 : CertificateAt 8 61 0 := by decide +kernel
theorem cell_8_61_1 : CertificateAt 8 61 1 := by decide +kernel
theorem cell_8_61_2 : CertificateAt 8 61 2 := by decide +kernel
theorem cell_8_61_3 : CertificateAt 8 61 3 := by decide +kernel
theorem cell_8_61_4 : CertificateAt 8 61 4 := by decide +kernel
theorem cell_8_61_5 : CertificateAt 8 61 5 := by decide +kernel
theorem row_8_61 : ThresholdAt 8 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 61 0 cell_8_61_0
    | exact certificate_sound 8 61 1 cell_8_61_1
    | exact certificate_sound 8 61 2 cell_8_61_2
    | exact certificate_sound 8 61 3 cell_8_61_3
    | exact certificate_sound 8 61 4 cell_8_61_4
    | exact certificate_sound 8 61 5 cell_8_61_5
theorem cell_8_62_0 : CertificateAt 8 62 0 := by decide +kernel
theorem cell_8_62_1 : CertificateAt 8 62 1 := by decide +kernel
theorem cell_8_62_2 : CertificateAt 8 62 2 := by decide +kernel
theorem cell_8_62_3 : CertificateAt 8 62 3 := by decide +kernel
theorem cell_8_62_4 : CertificateAt 8 62 4 := by decide +kernel
theorem cell_8_62_5 : CertificateAt 8 62 5 := by decide +kernel
theorem row_8_62 : ThresholdAt 8 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 62 0 cell_8_62_0
    | exact certificate_sound 8 62 1 cell_8_62_1
    | exact certificate_sound 8 62 2 cell_8_62_2
    | exact certificate_sound 8 62 3 cell_8_62_3
    | exact certificate_sound 8 62 4 cell_8_62_4
    | exact certificate_sound 8 62 5 cell_8_62_5
theorem cell_8_63_0 : CertificateAt 8 63 0 := by decide +kernel
theorem cell_8_63_1 : CertificateAt 8 63 1 := by decide +kernel
theorem cell_8_63_2 : CertificateAt 8 63 2 := by decide +kernel
theorem cell_8_63_3 : CertificateAt 8 63 3 := by decide +kernel
theorem cell_8_63_4 : CertificateAt 8 63 4 := by decide +kernel
theorem cell_8_63_5 : CertificateAt 8 63 5 := by decide +kernel
theorem row_8_63 : ThresholdAt 8 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 63 0 cell_8_63_0
    | exact certificate_sound 8 63 1 cell_8_63_1
    | exact certificate_sound 8 63 2 cell_8_63_2
    | exact certificate_sound 8 63 3 cell_8_63_3
    | exact certificate_sound 8 63 4 cell_8_63_4
    | exact certificate_sound 8 63 5 cell_8_63_5
theorem cell_8_64_0 : CertificateAt 8 64 0 := by decide +kernel
theorem cell_8_64_1 : CertificateAt 8 64 1 := by decide +kernel
theorem cell_8_64_2 : CertificateAt 8 64 2 := by decide +kernel
theorem cell_8_64_3 : CertificateAt 8 64 3 := by decide +kernel
theorem cell_8_64_4 : CertificateAt 8 64 4 := by decide +kernel
theorem cell_8_64_5 : CertificateAt 8 64 5 := by decide +kernel
theorem row_8_64 : ThresholdAt 8 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 64 0 cell_8_64_0
    | exact certificate_sound 8 64 1 cell_8_64_1
    | exact certificate_sound 8 64 2 cell_8_64_2
    | exact certificate_sound 8 64 3 cell_8_64_3
    | exact certificate_sound 8 64 4 cell_8_64_4
    | exact certificate_sound 8 64 5 cell_8_64_5
theorem cell_8_65_0 : CertificateAt 8 65 0 := by decide +kernel
theorem cell_8_65_1 : CertificateAt 8 65 1 := by decide +kernel
theorem cell_8_65_2 : CertificateAt 8 65 2 := by decide +kernel
theorem cell_8_65_3 : CertificateAt 8 65 3 := by decide +kernel
theorem cell_8_65_4 : CertificateAt 8 65 4 := by decide +kernel
theorem cell_8_65_5 : CertificateAt 8 65 5 := by decide +kernel
theorem row_8_65 : ThresholdAt 8 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 65 0 cell_8_65_0
    | exact certificate_sound 8 65 1 cell_8_65_1
    | exact certificate_sound 8 65 2 cell_8_65_2
    | exact certificate_sound 8 65 3 cell_8_65_3
    | exact certificate_sound 8 65 4 cell_8_65_4
    | exact certificate_sound 8 65 5 cell_8_65_5
theorem cell_8_66_0 : CertificateAt 8 66 0 := by decide +kernel
theorem cell_8_66_1 : CertificateAt 8 66 1 := by decide +kernel
theorem cell_8_66_2 : CertificateAt 8 66 2 := by decide +kernel
theorem cell_8_66_3 : CertificateAt 8 66 3 := by decide +kernel
theorem cell_8_66_4 : CertificateAt 8 66 4 := by decide +kernel
theorem cell_8_66_5 : CertificateAt 8 66 5 := by decide +kernel
theorem row_8_66 : ThresholdAt 8 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 66 0 cell_8_66_0
    | exact certificate_sound 8 66 1 cell_8_66_1
    | exact certificate_sound 8 66 2 cell_8_66_2
    | exact certificate_sound 8 66 3 cell_8_66_3
    | exact certificate_sound 8 66 4 cell_8_66_4
    | exact certificate_sound 8 66 5 cell_8_66_5
theorem cell_8_67_0 : CertificateAt 8 67 0 := by decide +kernel
theorem cell_8_67_1 : CertificateAt 8 67 1 := by decide +kernel
theorem cell_8_67_2 : CertificateAt 8 67 2 := by decide +kernel
theorem cell_8_67_3 : CertificateAt 8 67 3 := by decide +kernel
theorem cell_8_67_4 : CertificateAt 8 67 4 := by decide +kernel
theorem cell_8_67_5 : CertificateAt 8 67 5 := by decide +kernel
theorem row_8_67 : ThresholdAt 8 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 67 0 cell_8_67_0
    | exact certificate_sound 8 67 1 cell_8_67_1
    | exact certificate_sound 8 67 2 cell_8_67_2
    | exact certificate_sound 8 67 3 cell_8_67_3
    | exact certificate_sound 8 67 4 cell_8_67_4
    | exact certificate_sound 8 67 5 cell_8_67_5
theorem cell_8_68_0 : CertificateAt 8 68 0 := by decide +kernel
theorem cell_8_68_1 : CertificateAt 8 68 1 := by decide +kernel
theorem cell_8_68_2 : CertificateAt 8 68 2 := by decide +kernel
theorem cell_8_68_3 : CertificateAt 8 68 3 := by decide +kernel
theorem cell_8_68_4 : CertificateAt 8 68 4 := by decide +kernel
theorem cell_8_68_5 : CertificateAt 8 68 5 := by decide +kernel
theorem row_8_68 : ThresholdAt 8 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 68 0 cell_8_68_0
    | exact certificate_sound 8 68 1 cell_8_68_1
    | exact certificate_sound 8 68 2 cell_8_68_2
    | exact certificate_sound 8 68 3 cell_8_68_3
    | exact certificate_sound 8 68 4 cell_8_68_4
    | exact certificate_sound 8 68 5 cell_8_68_5
theorem cell_8_69_0 : CertificateAt 8 69 0 := by decide +kernel
theorem cell_8_69_1 : CertificateAt 8 69 1 := by decide +kernel
theorem cell_8_69_2 : CertificateAt 8 69 2 := by decide +kernel
theorem cell_8_69_3 : CertificateAt 8 69 3 := by decide +kernel
theorem cell_8_69_4 : CertificateAt 8 69 4 := by decide +kernel
theorem cell_8_69_5 : CertificateAt 8 69 5 := by decide +kernel
theorem row_8_69 : ThresholdAt 8 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 69 0 cell_8_69_0
    | exact certificate_sound 8 69 1 cell_8_69_1
    | exact certificate_sound 8 69 2 cell_8_69_2
    | exact certificate_sound 8 69 3 cell_8_69_3
    | exact certificate_sound 8 69 4 cell_8_69_4
    | exact certificate_sound 8 69 5 cell_8_69_5
theorem cell_8_70_0 : CertificateAt 8 70 0 := by decide +kernel
theorem cell_8_70_1 : CertificateAt 8 70 1 := by decide +kernel
theorem cell_8_70_2 : CertificateAt 8 70 2 := by decide +kernel
theorem cell_8_70_3 : CertificateAt 8 70 3 := by decide +kernel
theorem cell_8_70_4 : CertificateAt 8 70 4 := by decide +kernel
theorem cell_8_70_5 : CertificateAt 8 70 5 := by decide +kernel
theorem row_8_70 : ThresholdAt 8 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 70 0 cell_8_70_0
    | exact certificate_sound 8 70 1 cell_8_70_1
    | exact certificate_sound 8 70 2 cell_8_70_2
    | exact certificate_sound 8 70 3 cell_8_70_3
    | exact certificate_sound 8 70 4 cell_8_70_4
    | exact certificate_sound 8 70 5 cell_8_70_5
theorem cell_8_71_0 : CertificateAt 8 71 0 := by decide +kernel
theorem cell_8_71_1 : CertificateAt 8 71 1 := by decide +kernel
theorem cell_8_71_2 : CertificateAt 8 71 2 := by decide +kernel
theorem cell_8_71_3 : CertificateAt 8 71 3 := by decide +kernel
theorem cell_8_71_4 : CertificateAt 8 71 4 := by decide +kernel
theorem cell_8_71_5 : CertificateAt 8 71 5 := by decide +kernel
theorem row_8_71 : ThresholdAt 8 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 71 0 cell_8_71_0
    | exact certificate_sound 8 71 1 cell_8_71_1
    | exact certificate_sound 8 71 2 cell_8_71_2
    | exact certificate_sound 8 71 3 cell_8_71_3
    | exact certificate_sound 8 71 4 cell_8_71_4
    | exact certificate_sound 8 71 5 cell_8_71_5
theorem cell_8_72_0 : CertificateAt 8 72 0 := by decide +kernel
theorem cell_8_72_1 : CertificateAt 8 72 1 := by decide +kernel
theorem cell_8_72_2 : CertificateAt 8 72 2 := by decide +kernel
theorem cell_8_72_3 : CertificateAt 8 72 3 := by decide +kernel
theorem cell_8_72_4 : CertificateAt 8 72 4 := by decide +kernel
theorem cell_8_72_5 : CertificateAt 8 72 5 := by decide +kernel
theorem row_8_72 : ThresholdAt 8 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 72 0 cell_8_72_0
    | exact certificate_sound 8 72 1 cell_8_72_1
    | exact certificate_sound 8 72 2 cell_8_72_2
    | exact certificate_sound 8 72 3 cell_8_72_3
    | exact certificate_sound 8 72 4 cell_8_72_4
    | exact certificate_sound 8 72 5 cell_8_72_5
theorem cell_8_73_0 : CertificateAt 8 73 0 := by decide +kernel
theorem cell_8_73_1 : CertificateAt 8 73 1 := by decide +kernel
theorem cell_8_73_2 : CertificateAt 8 73 2 := by decide +kernel
theorem cell_8_73_3 : CertificateAt 8 73 3 := by decide +kernel
theorem cell_8_73_4 : CertificateAt 8 73 4 := by decide +kernel
theorem cell_8_73_5 : CertificateAt 8 73 5 := by decide +kernel
theorem row_8_73 : ThresholdAt 8 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 73 0 cell_8_73_0
    | exact certificate_sound 8 73 1 cell_8_73_1
    | exact certificate_sound 8 73 2 cell_8_73_2
    | exact certificate_sound 8 73 3 cell_8_73_3
    | exact certificate_sound 8 73 4 cell_8_73_4
    | exact certificate_sound 8 73 5 cell_8_73_5
theorem cell_8_74_0 : CertificateAt 8 74 0 := by decide +kernel
theorem cell_8_74_1 : CertificateAt 8 74 1 := by decide +kernel
theorem cell_8_74_2 : CertificateAt 8 74 2 := by decide +kernel
theorem cell_8_74_3 : CertificateAt 8 74 3 := by decide +kernel
theorem cell_8_74_4 : CertificateAt 8 74 4 := by decide +kernel
theorem cell_8_74_5 : CertificateAt 8 74 5 := by decide +kernel
theorem row_8_74 : ThresholdAt 8 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 74 0 cell_8_74_0
    | exact certificate_sound 8 74 1 cell_8_74_1
    | exact certificate_sound 8 74 2 cell_8_74_2
    | exact certificate_sound 8 74 3 cell_8_74_3
    | exact certificate_sound 8 74 4 cell_8_74_4
    | exact certificate_sound 8 74 5 cell_8_74_5
theorem cell_8_75_0 : CertificateAt 8 75 0 := by decide +kernel
theorem cell_8_75_1 : CertificateAt 8 75 1 := by decide +kernel
theorem cell_8_75_2 : CertificateAt 8 75 2 := by decide +kernel
theorem cell_8_75_3 : CertificateAt 8 75 3 := by decide +kernel
theorem cell_8_75_4 : CertificateAt 8 75 4 := by decide +kernel
theorem cell_8_75_5 : CertificateAt 8 75 5 := by decide +kernel
theorem row_8_75 : ThresholdAt 8 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 75 0 cell_8_75_0
    | exact certificate_sound 8 75 1 cell_8_75_1
    | exact certificate_sound 8 75 2 cell_8_75_2
    | exact certificate_sound 8 75 3 cell_8_75_3
    | exact certificate_sound 8 75 4 cell_8_75_4
    | exact certificate_sound 8 75 5 cell_8_75_5
theorem cell_8_76_0 : CertificateAt 8 76 0 := by decide +kernel
theorem cell_8_76_1 : CertificateAt 8 76 1 := by decide +kernel
theorem cell_8_76_2 : CertificateAt 8 76 2 := by decide +kernel
theorem cell_8_76_3 : CertificateAt 8 76 3 := by decide +kernel
theorem cell_8_76_4 : CertificateAt 8 76 4 := by decide +kernel
theorem cell_8_76_5 : CertificateAt 8 76 5 := by decide +kernel
theorem row_8_76 : ThresholdAt 8 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 76 0 cell_8_76_0
    | exact certificate_sound 8 76 1 cell_8_76_1
    | exact certificate_sound 8 76 2 cell_8_76_2
    | exact certificate_sound 8 76 3 cell_8_76_3
    | exact certificate_sound 8 76 4 cell_8_76_4
    | exact certificate_sound 8 76 5 cell_8_76_5
theorem cell_8_77_0 : CertificateAt 8 77 0 := by decide +kernel
theorem cell_8_77_1 : CertificateAt 8 77 1 := by decide +kernel
theorem cell_8_77_2 : CertificateAt 8 77 2 := by decide +kernel
theorem cell_8_77_3 : CertificateAt 8 77 3 := by decide +kernel
theorem cell_8_77_4 : CertificateAt 8 77 4 := by decide +kernel
theorem cell_8_77_5 : CertificateAt 8 77 5 := by decide +kernel
theorem row_8_77 : ThresholdAt 8 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 77 0 cell_8_77_0
    | exact certificate_sound 8 77 1 cell_8_77_1
    | exact certificate_sound 8 77 2 cell_8_77_2
    | exact certificate_sound 8 77 3 cell_8_77_3
    | exact certificate_sound 8 77 4 cell_8_77_4
    | exact certificate_sound 8 77 5 cell_8_77_5
theorem cell_8_78_0 : CertificateAt 8 78 0 := by decide +kernel
theorem cell_8_78_1 : CertificateAt 8 78 1 := by decide +kernel
theorem cell_8_78_2 : CertificateAt 8 78 2 := by decide +kernel
theorem cell_8_78_3 : CertificateAt 8 78 3 := by decide +kernel
theorem cell_8_78_4 : CertificateAt 8 78 4 := by decide +kernel
theorem cell_8_78_5 : CertificateAt 8 78 5 := by decide +kernel
theorem row_8_78 : ThresholdAt 8 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 78 0 cell_8_78_0
    | exact certificate_sound 8 78 1 cell_8_78_1
    | exact certificate_sound 8 78 2 cell_8_78_2
    | exact certificate_sound 8 78 3 cell_8_78_3
    | exact certificate_sound 8 78 4 cell_8_78_4
    | exact certificate_sound 8 78 5 cell_8_78_5
theorem cell_8_79_0 : CertificateAt 8 79 0 := by decide +kernel
theorem cell_8_79_1 : CertificateAt 8 79 1 := by decide +kernel
theorem cell_8_79_2 : CertificateAt 8 79 2 := by decide +kernel
theorem cell_8_79_3 : CertificateAt 8 79 3 := by decide +kernel
theorem cell_8_79_4 : CertificateAt 8 79 4 := by decide +kernel
theorem cell_8_79_5 : CertificateAt 8 79 5 := by decide +kernel
theorem row_8_79 : ThresholdAt 8 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 79 0 cell_8_79_0
    | exact certificate_sound 8 79 1 cell_8_79_1
    | exact certificate_sound 8 79 2 cell_8_79_2
    | exact certificate_sound 8 79 3 cell_8_79_3
    | exact certificate_sound 8 79 4 cell_8_79_4
    | exact certificate_sound 8 79 5 cell_8_79_5
theorem cell_8_80_0 : CertificateAt 8 80 0 := by decide +kernel
theorem cell_8_80_1 : CertificateAt 8 80 1 := by decide +kernel
theorem cell_8_80_2 : CertificateAt 8 80 2 := by decide +kernel
theorem cell_8_80_3 : CertificateAt 8 80 3 := by decide +kernel
theorem cell_8_80_4 : CertificateAt 8 80 4 := by decide +kernel
theorem cell_8_80_5 : CertificateAt 8 80 5 := by decide +kernel
theorem row_8_80 : ThresholdAt 8 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 80 0 cell_8_80_0
    | exact certificate_sound 8 80 1 cell_8_80_1
    | exact certificate_sound 8 80 2 cell_8_80_2
    | exact certificate_sound 8 80 3 cell_8_80_3
    | exact certificate_sound 8 80 4 cell_8_80_4
    | exact certificate_sound 8 80 5 cell_8_80_5
theorem cell_8_81_0 : CertificateAt 8 81 0 := by decide +kernel
theorem cell_8_81_1 : CertificateAt 8 81 1 := by decide +kernel
theorem cell_8_81_2 : CertificateAt 8 81 2 := by decide +kernel
theorem cell_8_81_3 : CertificateAt 8 81 3 := by decide +kernel
theorem cell_8_81_4 : CertificateAt 8 81 4 := by decide +kernel
theorem cell_8_81_5 : CertificateAt 8 81 5 := by decide +kernel
theorem row_8_81 : ThresholdAt 8 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 81 0 cell_8_81_0
    | exact certificate_sound 8 81 1 cell_8_81_1
    | exact certificate_sound 8 81 2 cell_8_81_2
    | exact certificate_sound 8 81 3 cell_8_81_3
    | exact certificate_sound 8 81 4 cell_8_81_4
    | exact certificate_sound 8 81 5 cell_8_81_5
theorem cell_8_82_0 : CertificateAt 8 82 0 := by decide +kernel
theorem cell_8_82_1 : CertificateAt 8 82 1 := by decide +kernel
theorem cell_8_82_2 : CertificateAt 8 82 2 := by decide +kernel
theorem cell_8_82_3 : CertificateAt 8 82 3 := by decide +kernel
theorem cell_8_82_4 : CertificateAt 8 82 4 := by decide +kernel
theorem cell_8_82_5 : CertificateAt 8 82 5 := by decide +kernel
theorem row_8_82 : ThresholdAt 8 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 82 0 cell_8_82_0
    | exact certificate_sound 8 82 1 cell_8_82_1
    | exact certificate_sound 8 82 2 cell_8_82_2
    | exact certificate_sound 8 82 3 cell_8_82_3
    | exact certificate_sound 8 82 4 cell_8_82_4
    | exact certificate_sound 8 82 5 cell_8_82_5
theorem cell_8_83_0 : CertificateAt 8 83 0 := by decide +kernel
theorem cell_8_83_1 : CertificateAt 8 83 1 := by decide +kernel
theorem cell_8_83_2 : CertificateAt 8 83 2 := by decide +kernel
theorem cell_8_83_3 : CertificateAt 8 83 3 := by decide +kernel
theorem cell_8_83_4 : CertificateAt 8 83 4 := by decide +kernel
theorem cell_8_83_5 : CertificateAt 8 83 5 := by decide +kernel
theorem row_8_83 : ThresholdAt 8 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 83 0 cell_8_83_0
    | exact certificate_sound 8 83 1 cell_8_83_1
    | exact certificate_sound 8 83 2 cell_8_83_2
    | exact certificate_sound 8 83 3 cell_8_83_3
    | exact certificate_sound 8 83 4 cell_8_83_4
    | exact certificate_sound 8 83 5 cell_8_83_5
theorem cell_8_84_0 : CertificateAt 8 84 0 := by decide +kernel
theorem cell_8_84_1 : CertificateAt 8 84 1 := by decide +kernel
theorem cell_8_84_2 : CertificateAt 8 84 2 := by decide +kernel
theorem cell_8_84_3 : CertificateAt 8 84 3 := by decide +kernel
theorem cell_8_84_4 : CertificateAt 8 84 4 := by decide +kernel
theorem cell_8_84_5 : CertificateAt 8 84 5 := by decide +kernel
theorem row_8_84 : ThresholdAt 8 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 84 0 cell_8_84_0
    | exact certificate_sound 8 84 1 cell_8_84_1
    | exact certificate_sound 8 84 2 cell_8_84_2
    | exact certificate_sound 8 84 3 cell_8_84_3
    | exact certificate_sound 8 84 4 cell_8_84_4
    | exact certificate_sound 8 84 5 cell_8_84_5
theorem cell_8_85_0 : CertificateAt 8 85 0 := by decide +kernel
theorem cell_8_85_1 : CertificateAt 8 85 1 := by decide +kernel
theorem cell_8_85_2 : CertificateAt 8 85 2 := by decide +kernel
theorem cell_8_85_3 : CertificateAt 8 85 3 := by decide +kernel
theorem cell_8_85_4 : CertificateAt 8 85 4 := by decide +kernel
theorem cell_8_85_5 : CertificateAt 8 85 5 := by decide +kernel
theorem row_8_85 : ThresholdAt 8 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 85 0 cell_8_85_0
    | exact certificate_sound 8 85 1 cell_8_85_1
    | exact certificate_sound 8 85 2 cell_8_85_2
    | exact certificate_sound 8 85 3 cell_8_85_3
    | exact certificate_sound 8 85 4 cell_8_85_4
    | exact certificate_sound 8 85 5 cell_8_85_5
theorem cell_8_86_0 : CertificateAt 8 86 0 := by decide +kernel
theorem cell_8_86_1 : CertificateAt 8 86 1 := by decide +kernel
theorem cell_8_86_2 : CertificateAt 8 86 2 := by decide +kernel
theorem cell_8_86_3 : CertificateAt 8 86 3 := by decide +kernel
theorem cell_8_86_4 : CertificateAt 8 86 4 := by decide +kernel
theorem cell_8_86_5 : CertificateAt 8 86 5 := by decide +kernel
theorem row_8_86 : ThresholdAt 8 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 86 0 cell_8_86_0
    | exact certificate_sound 8 86 1 cell_8_86_1
    | exact certificate_sound 8 86 2 cell_8_86_2
    | exact certificate_sound 8 86 3 cell_8_86_3
    | exact certificate_sound 8 86 4 cell_8_86_4
    | exact certificate_sound 8 86 5 cell_8_86_5
theorem cell_8_87_0 : CertificateAt 8 87 0 := by decide +kernel
theorem cell_8_87_1 : CertificateAt 8 87 1 := by decide +kernel
theorem cell_8_87_2 : CertificateAt 8 87 2 := by decide +kernel
theorem cell_8_87_3 : CertificateAt 8 87 3 := by decide +kernel
theorem cell_8_87_4 : CertificateAt 8 87 4 := by decide +kernel
theorem cell_8_87_5 : CertificateAt 8 87 5 := by decide +kernel
theorem row_8_87 : ThresholdAt 8 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 87 0 cell_8_87_0
    | exact certificate_sound 8 87 1 cell_8_87_1
    | exact certificate_sound 8 87 2 cell_8_87_2
    | exact certificate_sound 8 87 3 cell_8_87_3
    | exact certificate_sound 8 87 4 cell_8_87_4
    | exact certificate_sound 8 87 5 cell_8_87_5
theorem cell_8_88_0 : CertificateAt 8 88 0 := by decide +kernel
theorem cell_8_88_1 : CertificateAt 8 88 1 := by decide +kernel
theorem cell_8_88_2 : CertificateAt 8 88 2 := by decide +kernel
theorem cell_8_88_3 : CertificateAt 8 88 3 := by decide +kernel
theorem cell_8_88_4 : CertificateAt 8 88 4 := by decide +kernel
theorem cell_8_88_5 : CertificateAt 8 88 5 := by decide +kernel
theorem row_8_88 : ThresholdAt 8 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 88 0 cell_8_88_0
    | exact certificate_sound 8 88 1 cell_8_88_1
    | exact certificate_sound 8 88 2 cell_8_88_2
    | exact certificate_sound 8 88 3 cell_8_88_3
    | exact certificate_sound 8 88 4 cell_8_88_4
    | exact certificate_sound 8 88 5 cell_8_88_5
theorem cell_8_89_0 : CertificateAt 8 89 0 := by decide +kernel
theorem cell_8_89_1 : CertificateAt 8 89 1 := by decide +kernel
theorem cell_8_89_2 : CertificateAt 8 89 2 := by decide +kernel
theorem cell_8_89_3 : CertificateAt 8 89 3 := by decide +kernel
theorem cell_8_89_4 : CertificateAt 8 89 4 := by decide +kernel
theorem cell_8_89_5 : CertificateAt 8 89 5 := by decide +kernel
theorem row_8_89 : ThresholdAt 8 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 89 0 cell_8_89_0
    | exact certificate_sound 8 89 1 cell_8_89_1
    | exact certificate_sound 8 89 2 cell_8_89_2
    | exact certificate_sound 8 89 3 cell_8_89_3
    | exact certificate_sound 8 89 4 cell_8_89_4
    | exact certificate_sound 8 89 5 cell_8_89_5
theorem cell_8_90_0 : CertificateAt 8 90 0 := by decide +kernel
theorem cell_8_90_1 : CertificateAt 8 90 1 := by decide +kernel
theorem cell_8_90_2 : CertificateAt 8 90 2 := by decide +kernel
theorem cell_8_90_3 : CertificateAt 8 90 3 := by decide +kernel
theorem cell_8_90_4 : CertificateAt 8 90 4 := by decide +kernel
theorem cell_8_90_5 : CertificateAt 8 90 5 := by decide +kernel
theorem row_8_90 : ThresholdAt 8 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 90 0 cell_8_90_0
    | exact certificate_sound 8 90 1 cell_8_90_1
    | exact certificate_sound 8 90 2 cell_8_90_2
    | exact certificate_sound 8 90 3 cell_8_90_3
    | exact certificate_sound 8 90 4 cell_8_90_4
    | exact certificate_sound 8 90 5 cell_8_90_5
theorem cell_8_91_0 : CertificateAt 8 91 0 := by decide +kernel
theorem cell_8_91_1 : CertificateAt 8 91 1 := by decide +kernel
theorem cell_8_91_2 : CertificateAt 8 91 2 := by decide +kernel
theorem cell_8_91_3 : CertificateAt 8 91 3 := by decide +kernel
theorem cell_8_91_4 : CertificateAt 8 91 4 := by decide +kernel
theorem cell_8_91_5 : CertificateAt 8 91 5 := by decide +kernel
theorem row_8_91 : ThresholdAt 8 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 91 0 cell_8_91_0
    | exact certificate_sound 8 91 1 cell_8_91_1
    | exact certificate_sound 8 91 2 cell_8_91_2
    | exact certificate_sound 8 91 3 cell_8_91_3
    | exact certificate_sound 8 91 4 cell_8_91_4
    | exact certificate_sound 8 91 5 cell_8_91_5
theorem cell_8_92_0 : CertificateAt 8 92 0 := by decide +kernel
theorem cell_8_92_1 : CertificateAt 8 92 1 := by decide +kernel
theorem cell_8_92_2 : CertificateAt 8 92 2 := by decide +kernel
theorem cell_8_92_3 : CertificateAt 8 92 3 := by decide +kernel
theorem cell_8_92_4 : CertificateAt 8 92 4 := by decide +kernel
theorem cell_8_92_5 : CertificateAt 8 92 5 := by decide +kernel
theorem row_8_92 : ThresholdAt 8 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 92 0 cell_8_92_0
    | exact certificate_sound 8 92 1 cell_8_92_1
    | exact certificate_sound 8 92 2 cell_8_92_2
    | exact certificate_sound 8 92 3 cell_8_92_3
    | exact certificate_sound 8 92 4 cell_8_92_4
    | exact certificate_sound 8 92 5 cell_8_92_5
theorem cell_8_93_0 : CertificateAt 8 93 0 := by decide +kernel
theorem cell_8_93_1 : CertificateAt 8 93 1 := by decide +kernel
theorem cell_8_93_2 : CertificateAt 8 93 2 := by decide +kernel
theorem cell_8_93_3 : CertificateAt 8 93 3 := by decide +kernel
theorem cell_8_93_4 : CertificateAt 8 93 4 := by decide +kernel
theorem cell_8_93_5 : CertificateAt 8 93 5 := by decide +kernel
theorem row_8_93 : ThresholdAt 8 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 93 0 cell_8_93_0
    | exact certificate_sound 8 93 1 cell_8_93_1
    | exact certificate_sound 8 93 2 cell_8_93_2
    | exact certificate_sound 8 93 3 cell_8_93_3
    | exact certificate_sound 8 93 4 cell_8_93_4
    | exact certificate_sound 8 93 5 cell_8_93_5
theorem cell_8_94_0 : CertificateAt 8 94 0 := by decide +kernel
theorem cell_8_94_1 : CertificateAt 8 94 1 := by decide +kernel
theorem cell_8_94_2 : CertificateAt 8 94 2 := by decide +kernel
theorem cell_8_94_3 : CertificateAt 8 94 3 := by decide +kernel
theorem cell_8_94_4 : CertificateAt 8 94 4 := by decide +kernel
theorem cell_8_94_5 : CertificateAt 8 94 5 := by decide +kernel
theorem row_8_94 : ThresholdAt 8 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 94 0 cell_8_94_0
    | exact certificate_sound 8 94 1 cell_8_94_1
    | exact certificate_sound 8 94 2 cell_8_94_2
    | exact certificate_sound 8 94 3 cell_8_94_3
    | exact certificate_sound 8 94 4 cell_8_94_4
    | exact certificate_sound 8 94 5 cell_8_94_5
theorem cell_8_95_0 : CertificateAt 8 95 0 := by decide +kernel
theorem cell_8_95_1 : CertificateAt 8 95 1 := by decide +kernel
theorem cell_8_95_2 : CertificateAt 8 95 2 := by decide +kernel
theorem cell_8_95_3 : CertificateAt 8 95 3 := by decide +kernel
theorem cell_8_95_4 : CertificateAt 8 95 4 := by decide +kernel
theorem cell_8_95_5 : CertificateAt 8 95 5 := by decide +kernel
theorem row_8_95 : ThresholdAt 8 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 95 0 cell_8_95_0
    | exact certificate_sound 8 95 1 cell_8_95_1
    | exact certificate_sound 8 95 2 cell_8_95_2
    | exact certificate_sound 8 95 3 cell_8_95_3
    | exact certificate_sound 8 95 4 cell_8_95_4
    | exact certificate_sound 8 95 5 cell_8_95_5
theorem cell_8_96_0 : CertificateAt 8 96 0 := by decide +kernel
theorem cell_8_96_1 : CertificateAt 8 96 1 := by decide +kernel
theorem cell_8_96_2 : CertificateAt 8 96 2 := by decide +kernel
theorem cell_8_96_3 : CertificateAt 8 96 3 := by decide +kernel
theorem cell_8_96_4 : CertificateAt 8 96 4 := by decide +kernel
theorem cell_8_96_5 : CertificateAt 8 96 5 := by decide +kernel
theorem row_8_96 : ThresholdAt 8 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 96 0 cell_8_96_0
    | exact certificate_sound 8 96 1 cell_8_96_1
    | exact certificate_sound 8 96 2 cell_8_96_2
    | exact certificate_sound 8 96 3 cell_8_96_3
    | exact certificate_sound 8 96 4 cell_8_96_4
    | exact certificate_sound 8 96 5 cell_8_96_5
theorem cell_8_97_0 : CertificateAt 8 97 0 := by decide +kernel
theorem cell_8_97_1 : CertificateAt 8 97 1 := by decide +kernel
theorem cell_8_97_2 : CertificateAt 8 97 2 := by decide +kernel
theorem cell_8_97_3 : CertificateAt 8 97 3 := by decide +kernel
theorem cell_8_97_4 : CertificateAt 8 97 4 := by decide +kernel
theorem cell_8_97_5 : CertificateAt 8 97 5 := by decide +kernel
theorem row_8_97 : ThresholdAt 8 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 97 0 cell_8_97_0
    | exact certificate_sound 8 97 1 cell_8_97_1
    | exact certificate_sound 8 97 2 cell_8_97_2
    | exact certificate_sound 8 97 3 cell_8_97_3
    | exact certificate_sound 8 97 4 cell_8_97_4
    | exact certificate_sound 8 97 5 cell_8_97_5
theorem cell_8_98_0 : CertificateAt 8 98 0 := by decide +kernel
theorem cell_8_98_1 : CertificateAt 8 98 1 := by decide +kernel
theorem cell_8_98_2 : CertificateAt 8 98 2 := by decide +kernel
theorem cell_8_98_3 : CertificateAt 8 98 3 := by decide +kernel
theorem cell_8_98_4 : CertificateAt 8 98 4 := by decide +kernel
theorem cell_8_98_5 : CertificateAt 8 98 5 := by decide +kernel
theorem row_8_98 : ThresholdAt 8 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 98 0 cell_8_98_0
    | exact certificate_sound 8 98 1 cell_8_98_1
    | exact certificate_sound 8 98 2 cell_8_98_2
    | exact certificate_sound 8 98 3 cell_8_98_3
    | exact certificate_sound 8 98 4 cell_8_98_4
    | exact certificate_sound 8 98 5 cell_8_98_5
theorem cell_8_99_0 : CertificateAt 8 99 0 := by decide +kernel
theorem cell_8_99_1 : CertificateAt 8 99 1 := by decide +kernel
theorem cell_8_99_2 : CertificateAt 8 99 2 := by decide +kernel
theorem cell_8_99_3 : CertificateAt 8 99 3 := by decide +kernel
theorem cell_8_99_4 : CertificateAt 8 99 4 := by decide +kernel
theorem cell_8_99_5 : CertificateAt 8 99 5 := by decide +kernel
theorem row_8_99 : ThresholdAt 8 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 99 0 cell_8_99_0
    | exact certificate_sound 8 99 1 cell_8_99_1
    | exact certificate_sound 8 99 2 cell_8_99_2
    | exact certificate_sound 8 99 3 cell_8_99_3
    | exact certificate_sound 8 99 4 cell_8_99_4
    | exact certificate_sound 8 99 5 cell_8_99_5
theorem cell_8_100_0 : CertificateAt 8 100 0 := by decide +kernel
theorem cell_8_100_1 : CertificateAt 8 100 1 := by decide +kernel
theorem cell_8_100_2 : CertificateAt 8 100 2 := by decide +kernel
theorem cell_8_100_3 : CertificateAt 8 100 3 := by decide +kernel
theorem cell_8_100_4 : CertificateAt 8 100 4 := by decide +kernel
theorem cell_8_100_5 : CertificateAt 8 100 5 := by decide +kernel
theorem row_8_100 : ThresholdAt 8 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 100 0 cell_8_100_0
    | exact certificate_sound 8 100 1 cell_8_100_1
    | exact certificate_sound 8 100 2 cell_8_100_2
    | exact certificate_sound 8 100 3 cell_8_100_3
    | exact certificate_sound 8 100 4 cell_8_100_4
    | exact certificate_sound 8 100 5 cell_8_100_5
theorem cell_8_101_0 : CertificateAt 8 101 0 := by decide +kernel
theorem cell_8_101_1 : CertificateAt 8 101 1 := by decide +kernel
theorem cell_8_101_2 : CertificateAt 8 101 2 := by decide +kernel
theorem cell_8_101_3 : CertificateAt 8 101 3 := by decide +kernel
theorem cell_8_101_4 : CertificateAt 8 101 4 := by decide +kernel
theorem cell_8_101_5 : CertificateAt 8 101 5 := by decide +kernel
theorem row_8_101 : ThresholdAt 8 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 101 0 cell_8_101_0
    | exact certificate_sound 8 101 1 cell_8_101_1
    | exact certificate_sound 8 101 2 cell_8_101_2
    | exact certificate_sound 8 101 3 cell_8_101_3
    | exact certificate_sound 8 101 4 cell_8_101_4
    | exact certificate_sound 8 101 5 cell_8_101_5
theorem cell_8_102_0 : CertificateAt 8 102 0 := by decide +kernel
theorem cell_8_102_1 : CertificateAt 8 102 1 := by decide +kernel
theorem cell_8_102_2 : CertificateAt 8 102 2 := by decide +kernel
theorem cell_8_102_3 : CertificateAt 8 102 3 := by decide +kernel
theorem cell_8_102_4 : CertificateAt 8 102 4 := by decide +kernel
theorem cell_8_102_5 : CertificateAt 8 102 5 := by decide +kernel
theorem row_8_102 : ThresholdAt 8 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 102 0 cell_8_102_0
    | exact certificate_sound 8 102 1 cell_8_102_1
    | exact certificate_sound 8 102 2 cell_8_102_2
    | exact certificate_sound 8 102 3 cell_8_102_3
    | exact certificate_sound 8 102 4 cell_8_102_4
    | exact certificate_sound 8 102 5 cell_8_102_5
theorem cell_8_103_0 : CertificateAt 8 103 0 := by decide +kernel
theorem cell_8_103_1 : CertificateAt 8 103 1 := by decide +kernel
theorem cell_8_103_2 : CertificateAt 8 103 2 := by decide +kernel
theorem cell_8_103_3 : CertificateAt 8 103 3 := by decide +kernel
theorem cell_8_103_4 : CertificateAt 8 103 4 := by decide +kernel
theorem cell_8_103_5 : CertificateAt 8 103 5 := by decide +kernel
theorem row_8_103 : ThresholdAt 8 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 103 0 cell_8_103_0
    | exact certificate_sound 8 103 1 cell_8_103_1
    | exact certificate_sound 8 103 2 cell_8_103_2
    | exact certificate_sound 8 103 3 cell_8_103_3
    | exact certificate_sound 8 103 4 cell_8_103_4
    | exact certificate_sound 8 103 5 cell_8_103_5
theorem cell_8_104_0 : CertificateAt 8 104 0 := by decide +kernel
theorem cell_8_104_1 : CertificateAt 8 104 1 := by decide +kernel
theorem cell_8_104_2 : CertificateAt 8 104 2 := by decide +kernel
theorem cell_8_104_3 : CertificateAt 8 104 3 := by decide +kernel
theorem cell_8_104_4 : CertificateAt 8 104 4 := by decide +kernel
theorem cell_8_104_5 : CertificateAt 8 104 5 := by decide +kernel
theorem row_8_104 : ThresholdAt 8 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 104 0 cell_8_104_0
    | exact certificate_sound 8 104 1 cell_8_104_1
    | exact certificate_sound 8 104 2 cell_8_104_2
    | exact certificate_sound 8 104 3 cell_8_104_3
    | exact certificate_sound 8 104 4 cell_8_104_4
    | exact certificate_sound 8 104 5 cell_8_104_5
theorem cell_8_105_0 : CertificateAt 8 105 0 := by decide +kernel
theorem cell_8_105_1 : CertificateAt 8 105 1 := by decide +kernel
theorem cell_8_105_2 : CertificateAt 8 105 2 := by decide +kernel
theorem cell_8_105_3 : CertificateAt 8 105 3 := by decide +kernel
theorem cell_8_105_4 : CertificateAt 8 105 4 := by decide +kernel
theorem cell_8_105_5 : CertificateAt 8 105 5 := by decide +kernel
theorem row_8_105 : ThresholdAt 8 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 105 0 cell_8_105_0
    | exact certificate_sound 8 105 1 cell_8_105_1
    | exact certificate_sound 8 105 2 cell_8_105_2
    | exact certificate_sound 8 105 3 cell_8_105_3
    | exact certificate_sound 8 105 4 cell_8_105_4
    | exact certificate_sound 8 105 5 cell_8_105_5
theorem cell_8_106_0 : CertificateAt 8 106 0 := by decide +kernel
theorem cell_8_106_1 : CertificateAt 8 106 1 := by decide +kernel
theorem cell_8_106_2 : CertificateAt 8 106 2 := by decide +kernel
theorem cell_8_106_3 : CertificateAt 8 106 3 := by decide +kernel
theorem cell_8_106_4 : CertificateAt 8 106 4 := by decide +kernel
theorem cell_8_106_5 : CertificateAt 8 106 5 := by decide +kernel
theorem row_8_106 : ThresholdAt 8 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 106 0 cell_8_106_0
    | exact certificate_sound 8 106 1 cell_8_106_1
    | exact certificate_sound 8 106 2 cell_8_106_2
    | exact certificate_sound 8 106 3 cell_8_106_3
    | exact certificate_sound 8 106 4 cell_8_106_4
    | exact certificate_sound 8 106 5 cell_8_106_5
theorem cell_8_107_0 : CertificateAt 8 107 0 := by decide +kernel
theorem cell_8_107_1 : CertificateAt 8 107 1 := by decide +kernel
theorem cell_8_107_2 : CertificateAt 8 107 2 := by decide +kernel
theorem cell_8_107_3 : CertificateAt 8 107 3 := by decide +kernel
theorem cell_8_107_4 : CertificateAt 8 107 4 := by decide +kernel
theorem cell_8_107_5 : CertificateAt 8 107 5 := by decide +kernel
theorem row_8_107 : ThresholdAt 8 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 107 0 cell_8_107_0
    | exact certificate_sound 8 107 1 cell_8_107_1
    | exact certificate_sound 8 107 2 cell_8_107_2
    | exact certificate_sound 8 107 3 cell_8_107_3
    | exact certificate_sound 8 107 4 cell_8_107_4
    | exact certificate_sound 8 107 5 cell_8_107_5
theorem cell_8_108_0 : CertificateAt 8 108 0 := by decide +kernel
theorem cell_8_108_1 : CertificateAt 8 108 1 := by decide +kernel
theorem cell_8_108_2 : CertificateAt 8 108 2 := by decide +kernel
theorem cell_8_108_3 : CertificateAt 8 108 3 := by decide +kernel
theorem cell_8_108_4 : CertificateAt 8 108 4 := by decide +kernel
theorem cell_8_108_5 : CertificateAt 8 108 5 := by decide +kernel
theorem row_8_108 : ThresholdAt 8 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 108 0 cell_8_108_0
    | exact certificate_sound 8 108 1 cell_8_108_1
    | exact certificate_sound 8 108 2 cell_8_108_2
    | exact certificate_sound 8 108 3 cell_8_108_3
    | exact certificate_sound 8 108 4 cell_8_108_4
    | exact certificate_sound 8 108 5 cell_8_108_5
theorem cell_8_109_0 : CertificateAt 8 109 0 := by decide +kernel
theorem cell_8_109_1 : CertificateAt 8 109 1 := by decide +kernel
theorem cell_8_109_2 : CertificateAt 8 109 2 := by decide +kernel
theorem cell_8_109_3 : CertificateAt 8 109 3 := by decide +kernel
theorem cell_8_109_4 : CertificateAt 8 109 4 := by decide +kernel
theorem cell_8_109_5 : CertificateAt 8 109 5 := by decide +kernel
theorem row_8_109 : ThresholdAt 8 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 109 0 cell_8_109_0
    | exact certificate_sound 8 109 1 cell_8_109_1
    | exact certificate_sound 8 109 2 cell_8_109_2
    | exact certificate_sound 8 109 3 cell_8_109_3
    | exact certificate_sound 8 109 4 cell_8_109_4
    | exact certificate_sound 8 109 5 cell_8_109_5
theorem cell_8_110_0 : CertificateAt 8 110 0 := by decide +kernel
theorem cell_8_110_1 : CertificateAt 8 110 1 := by decide +kernel
theorem cell_8_110_2 : CertificateAt 8 110 2 := by decide +kernel
theorem cell_8_110_3 : CertificateAt 8 110 3 := by decide +kernel
theorem cell_8_110_4 : CertificateAt 8 110 4 := by decide +kernel
theorem cell_8_110_5 : CertificateAt 8 110 5 := by decide +kernel
theorem row_8_110 : ThresholdAt 8 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 110 0 cell_8_110_0
    | exact certificate_sound 8 110 1 cell_8_110_1
    | exact certificate_sound 8 110 2 cell_8_110_2
    | exact certificate_sound 8 110 3 cell_8_110_3
    | exact certificate_sound 8 110 4 cell_8_110_4
    | exact certificate_sound 8 110 5 cell_8_110_5
theorem cell_8_111_0 : CertificateAt 8 111 0 := by decide +kernel
theorem cell_8_111_1 : CertificateAt 8 111 1 := by decide +kernel
theorem cell_8_111_2 : CertificateAt 8 111 2 := by decide +kernel
theorem cell_8_111_3 : CertificateAt 8 111 3 := by decide +kernel
theorem cell_8_111_4 : CertificateAt 8 111 4 := by decide +kernel
theorem cell_8_111_5 : CertificateAt 8 111 5 := by decide +kernel
theorem row_8_111 : ThresholdAt 8 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 111 0 cell_8_111_0
    | exact certificate_sound 8 111 1 cell_8_111_1
    | exact certificate_sound 8 111 2 cell_8_111_2
    | exact certificate_sound 8 111 3 cell_8_111_3
    | exact certificate_sound 8 111 4 cell_8_111_4
    | exact certificate_sound 8 111 5 cell_8_111_5
theorem cell_8_112_0 : CertificateAt 8 112 0 := by decide +kernel
theorem cell_8_112_1 : CertificateAt 8 112 1 := by decide +kernel
theorem cell_8_112_2 : CertificateAt 8 112 2 := by decide +kernel
theorem cell_8_112_3 : CertificateAt 8 112 3 := by decide +kernel
theorem cell_8_112_4 : CertificateAt 8 112 4 := by decide +kernel
theorem cell_8_112_5 : CertificateAt 8 112 5 := by decide +kernel
theorem row_8_112 : ThresholdAt 8 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 112 0 cell_8_112_0
    | exact certificate_sound 8 112 1 cell_8_112_1
    | exact certificate_sound 8 112 2 cell_8_112_2
    | exact certificate_sound 8 112 3 cell_8_112_3
    | exact certificate_sound 8 112 4 cell_8_112_4
    | exact certificate_sound 8 112 5 cell_8_112_5
theorem cell_8_113_0 : CertificateAt 8 113 0 := by decide +kernel
theorem cell_8_113_1 : CertificateAt 8 113 1 := by decide +kernel
theorem cell_8_113_2 : CertificateAt 8 113 2 := by decide +kernel
theorem cell_8_113_3 : CertificateAt 8 113 3 := by decide +kernel
theorem cell_8_113_4 : CertificateAt 8 113 4 := by decide +kernel
theorem cell_8_113_5 : CertificateAt 8 113 5 := by decide +kernel
theorem row_8_113 : ThresholdAt 8 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 113 0 cell_8_113_0
    | exact certificate_sound 8 113 1 cell_8_113_1
    | exact certificate_sound 8 113 2 cell_8_113_2
    | exact certificate_sound 8 113 3 cell_8_113_3
    | exact certificate_sound 8 113 4 cell_8_113_4
    | exact certificate_sound 8 113 5 cell_8_113_5
theorem cell_8_114_0 : CertificateAt 8 114 0 := by decide +kernel
theorem cell_8_114_1 : CertificateAt 8 114 1 := by decide +kernel
theorem cell_8_114_2 : CertificateAt 8 114 2 := by decide +kernel
theorem cell_8_114_3 : CertificateAt 8 114 3 := by decide +kernel
theorem cell_8_114_4 : CertificateAt 8 114 4 := by decide +kernel
theorem cell_8_114_5 : CertificateAt 8 114 5 := by decide +kernel
theorem row_8_114 : ThresholdAt 8 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 114 0 cell_8_114_0
    | exact certificate_sound 8 114 1 cell_8_114_1
    | exact certificate_sound 8 114 2 cell_8_114_2
    | exact certificate_sound 8 114 3 cell_8_114_3
    | exact certificate_sound 8 114 4 cell_8_114_4
    | exact certificate_sound 8 114 5 cell_8_114_5
theorem cell_8_115_0 : CertificateAt 8 115 0 := by decide +kernel
theorem cell_8_115_1 : CertificateAt 8 115 1 := by decide +kernel
theorem cell_8_115_2 : CertificateAt 8 115 2 := by decide +kernel
theorem cell_8_115_3 : CertificateAt 8 115 3 := by decide +kernel
theorem cell_8_115_4 : CertificateAt 8 115 4 := by decide +kernel
theorem cell_8_115_5 : CertificateAt 8 115 5 := by decide +kernel
theorem row_8_115 : ThresholdAt 8 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 115 0 cell_8_115_0
    | exact certificate_sound 8 115 1 cell_8_115_1
    | exact certificate_sound 8 115 2 cell_8_115_2
    | exact certificate_sound 8 115 3 cell_8_115_3
    | exact certificate_sound 8 115 4 cell_8_115_4
    | exact certificate_sound 8 115 5 cell_8_115_5
theorem cell_8_116_0 : CertificateAt 8 116 0 := by decide +kernel
theorem cell_8_116_1 : CertificateAt 8 116 1 := by decide +kernel
theorem cell_8_116_2 : CertificateAt 8 116 2 := by decide +kernel
theorem cell_8_116_3 : CertificateAt 8 116 3 := by decide +kernel
theorem cell_8_116_4 : CertificateAt 8 116 4 := by decide +kernel
theorem cell_8_116_5 : CertificateAt 8 116 5 := by decide +kernel
theorem row_8_116 : ThresholdAt 8 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 116 0 cell_8_116_0
    | exact certificate_sound 8 116 1 cell_8_116_1
    | exact certificate_sound 8 116 2 cell_8_116_2
    | exact certificate_sound 8 116 3 cell_8_116_3
    | exact certificate_sound 8 116 4 cell_8_116_4
    | exact certificate_sound 8 116 5 cell_8_116_5
theorem cell_8_117_0 : CertificateAt 8 117 0 := by decide +kernel
theorem cell_8_117_1 : CertificateAt 8 117 1 := by decide +kernel
theorem cell_8_117_2 : CertificateAt 8 117 2 := by decide +kernel
theorem cell_8_117_3 : CertificateAt 8 117 3 := by decide +kernel
theorem cell_8_117_4 : CertificateAt 8 117 4 := by decide +kernel
theorem cell_8_117_5 : CertificateAt 8 117 5 := by decide +kernel
theorem row_8_117 : ThresholdAt 8 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 117 0 cell_8_117_0
    | exact certificate_sound 8 117 1 cell_8_117_1
    | exact certificate_sound 8 117 2 cell_8_117_2
    | exact certificate_sound 8 117 3 cell_8_117_3
    | exact certificate_sound 8 117 4 cell_8_117_4
    | exact certificate_sound 8 117 5 cell_8_117_5
theorem cell_8_118_0 : CertificateAt 8 118 0 := by decide +kernel
theorem cell_8_118_1 : CertificateAt 8 118 1 := by decide +kernel
theorem cell_8_118_2 : CertificateAt 8 118 2 := by decide +kernel
theorem cell_8_118_3 : CertificateAt 8 118 3 := by decide +kernel
theorem cell_8_118_4 : CertificateAt 8 118 4 := by decide +kernel
theorem cell_8_118_5 : CertificateAt 8 118 5 := by decide +kernel
theorem row_8_118 : ThresholdAt 8 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 118 0 cell_8_118_0
    | exact certificate_sound 8 118 1 cell_8_118_1
    | exact certificate_sound 8 118 2 cell_8_118_2
    | exact certificate_sound 8 118 3 cell_8_118_3
    | exact certificate_sound 8 118 4 cell_8_118_4
    | exact certificate_sound 8 118 5 cell_8_118_5
theorem cell_8_119_0 : CertificateAt 8 119 0 := by decide +kernel
theorem cell_8_119_1 : CertificateAt 8 119 1 := by decide +kernel
theorem cell_8_119_2 : CertificateAt 8 119 2 := by decide +kernel
theorem cell_8_119_3 : CertificateAt 8 119 3 := by decide +kernel
theorem cell_8_119_4 : CertificateAt 8 119 4 := by decide +kernel
theorem cell_8_119_5 : CertificateAt 8 119 5 := by decide +kernel
theorem row_8_119 : ThresholdAt 8 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 119 0 cell_8_119_0
    | exact certificate_sound 8 119 1 cell_8_119_1
    | exact certificate_sound 8 119 2 cell_8_119_2
    | exact certificate_sound 8 119 3 cell_8_119_3
    | exact certificate_sound 8 119 4 cell_8_119_4
    | exact certificate_sound 8 119 5 cell_8_119_5
theorem cell_8_120_0 : CertificateAt 8 120 0 := by decide +kernel
theorem cell_8_120_1 : CertificateAt 8 120 1 := by decide +kernel
theorem cell_8_120_2 : CertificateAt 8 120 2 := by decide +kernel
theorem cell_8_120_3 : CertificateAt 8 120 3 := by decide +kernel
theorem cell_8_120_4 : CertificateAt 8 120 4 := by decide +kernel
theorem cell_8_120_5 : CertificateAt 8 120 5 := by decide +kernel
theorem row_8_120 : ThresholdAt 8 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 120 0 cell_8_120_0
    | exact certificate_sound 8 120 1 cell_8_120_1
    | exact certificate_sound 8 120 2 cell_8_120_2
    | exact certificate_sound 8 120 3 cell_8_120_3
    | exact certificate_sound 8 120 4 cell_8_120_4
    | exact certificate_sound 8 120 5 cell_8_120_5
theorem cell_8_121_0 : CertificateAt 8 121 0 := by decide +kernel
theorem cell_8_121_1 : CertificateAt 8 121 1 := by decide +kernel
theorem cell_8_121_2 : CertificateAt 8 121 2 := by decide +kernel
theorem cell_8_121_3 : CertificateAt 8 121 3 := by decide +kernel
theorem cell_8_121_4 : CertificateAt 8 121 4 := by decide +kernel
theorem cell_8_121_5 : CertificateAt 8 121 5 := by decide +kernel
theorem row_8_121 : ThresholdAt 8 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 121 0 cell_8_121_0
    | exact certificate_sound 8 121 1 cell_8_121_1
    | exact certificate_sound 8 121 2 cell_8_121_2
    | exact certificate_sound 8 121 3 cell_8_121_3
    | exact certificate_sound 8 121 4 cell_8_121_4
    | exact certificate_sound 8 121 5 cell_8_121_5
theorem cell_8_122_0 : CertificateAt 8 122 0 := by decide +kernel
theorem cell_8_122_1 : CertificateAt 8 122 1 := by decide +kernel
theorem cell_8_122_2 : CertificateAt 8 122 2 := by decide +kernel
theorem cell_8_122_3 : CertificateAt 8 122 3 := by decide +kernel
theorem cell_8_122_4 : CertificateAt 8 122 4 := by decide +kernel
theorem cell_8_122_5 : CertificateAt 8 122 5 := by decide +kernel
theorem row_8_122 : ThresholdAt 8 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 122 0 cell_8_122_0
    | exact certificate_sound 8 122 1 cell_8_122_1
    | exact certificate_sound 8 122 2 cell_8_122_2
    | exact certificate_sound 8 122 3 cell_8_122_3
    | exact certificate_sound 8 122 4 cell_8_122_4
    | exact certificate_sound 8 122 5 cell_8_122_5
theorem cell_8_123_0 : CertificateAt 8 123 0 := by decide +kernel
theorem cell_8_123_1 : CertificateAt 8 123 1 := by decide +kernel
theorem cell_8_123_2 : CertificateAt 8 123 2 := by decide +kernel
theorem cell_8_123_3 : CertificateAt 8 123 3 := by decide +kernel
theorem cell_8_123_4 : CertificateAt 8 123 4 := by decide +kernel
theorem cell_8_123_5 : CertificateAt 8 123 5 := by decide +kernel
theorem row_8_123 : ThresholdAt 8 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 123 0 cell_8_123_0
    | exact certificate_sound 8 123 1 cell_8_123_1
    | exact certificate_sound 8 123 2 cell_8_123_2
    | exact certificate_sound 8 123 3 cell_8_123_3
    | exact certificate_sound 8 123 4 cell_8_123_4
    | exact certificate_sound 8 123 5 cell_8_123_5
theorem cell_8_124_0 : CertificateAt 8 124 0 := by decide +kernel
theorem cell_8_124_1 : CertificateAt 8 124 1 := by decide +kernel
theorem cell_8_124_2 : CertificateAt 8 124 2 := by decide +kernel
theorem cell_8_124_3 : CertificateAt 8 124 3 := by decide +kernel
theorem cell_8_124_4 : CertificateAt 8 124 4 := by decide +kernel
theorem cell_8_124_5 : CertificateAt 8 124 5 := by decide +kernel
theorem row_8_124 : ThresholdAt 8 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 124 0 cell_8_124_0
    | exact certificate_sound 8 124 1 cell_8_124_1
    | exact certificate_sound 8 124 2 cell_8_124_2
    | exact certificate_sound 8 124 3 cell_8_124_3
    | exact certificate_sound 8 124 4 cell_8_124_4
    | exact certificate_sound 8 124 5 cell_8_124_5
theorem cell_8_125_0 : CertificateAt 8 125 0 := by decide +kernel
theorem cell_8_125_1 : CertificateAt 8 125 1 := by decide +kernel
theorem cell_8_125_2 : CertificateAt 8 125 2 := by decide +kernel
theorem cell_8_125_3 : CertificateAt 8 125 3 := by decide +kernel
theorem cell_8_125_4 : CertificateAt 8 125 4 := by decide +kernel
theorem cell_8_125_5 : CertificateAt 8 125 5 := by decide +kernel
theorem row_8_125 : ThresholdAt 8 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 125 0 cell_8_125_0
    | exact certificate_sound 8 125 1 cell_8_125_1
    | exact certificate_sound 8 125 2 cell_8_125_2
    | exact certificate_sound 8 125 3 cell_8_125_3
    | exact certificate_sound 8 125 4 cell_8_125_4
    | exact certificate_sound 8 125 5 cell_8_125_5
theorem cell_8_126_0 : CertificateAt 8 126 0 := by decide +kernel
theorem cell_8_126_1 : CertificateAt 8 126 1 := by decide +kernel
theorem cell_8_126_2 : CertificateAt 8 126 2 := by decide +kernel
theorem cell_8_126_3 : CertificateAt 8 126 3 := by decide +kernel
theorem cell_8_126_4 : CertificateAt 8 126 4 := by decide +kernel
theorem cell_8_126_5 : CertificateAt 8 126 5 := by decide +kernel
theorem row_8_126 : ThresholdAt 8 126 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 126 0 cell_8_126_0
    | exact certificate_sound 8 126 1 cell_8_126_1
    | exact certificate_sound 8 126 2 cell_8_126_2
    | exact certificate_sound 8 126 3 cell_8_126_3
    | exact certificate_sound 8 126 4 cell_8_126_4
    | exact certificate_sound 8 126 5 cell_8_126_5
theorem cell_8_127_0 : CertificateAt 8 127 0 := by decide +kernel
theorem cell_8_127_1 : CertificateAt 8 127 1 := by decide +kernel
theorem cell_8_127_2 : CertificateAt 8 127 2 := by decide +kernel
theorem cell_8_127_3 : CertificateAt 8 127 3 := by decide +kernel
theorem cell_8_127_4 : CertificateAt 8 127 4 := by decide +kernel
theorem cell_8_127_5 : CertificateAt 8 127 5 := by decide +kernel
theorem row_8_127 : ThresholdAt 8 127 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 127 0 cell_8_127_0
    | exact certificate_sound 8 127 1 cell_8_127_1
    | exact certificate_sound 8 127 2 cell_8_127_2
    | exact certificate_sound 8 127 3 cell_8_127_3
    | exact certificate_sound 8 127 4 cell_8_127_4
    | exact certificate_sound 8 127 5 cell_8_127_5
theorem cell_8_128_0 : CertificateAt 8 128 0 := by decide +kernel
theorem cell_8_128_1 : CertificateAt 8 128 1 := by decide +kernel
theorem cell_8_128_2 : CertificateAt 8 128 2 := by decide +kernel
theorem cell_8_128_3 : CertificateAt 8 128 3 := by decide +kernel
theorem cell_8_128_4 : CertificateAt 8 128 4 := by decide +kernel
theorem cell_8_128_5 : CertificateAt 8 128 5 := by decide +kernel
theorem row_8_128 : ThresholdAt 8 128 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 128 0 cell_8_128_0
    | exact certificate_sound 8 128 1 cell_8_128_1
    | exact certificate_sound 8 128 2 cell_8_128_2
    | exact certificate_sound 8 128 3 cell_8_128_3
    | exact certificate_sound 8 128 4 cell_8_128_4
    | exact certificate_sound 8 128 5 cell_8_128_5
theorem cell_8_129_0 : CertificateAt 8 129 0 := by decide +kernel
theorem cell_8_129_1 : CertificateAt 8 129 1 := by decide +kernel
theorem cell_8_129_2 : CertificateAt 8 129 2 := by decide +kernel
theorem cell_8_129_3 : CertificateAt 8 129 3 := by decide +kernel
theorem cell_8_129_4 : CertificateAt 8 129 4 := by decide +kernel
theorem cell_8_129_5 : CertificateAt 8 129 5 := by decide +kernel
theorem row_8_129 : ThresholdAt 8 129 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 129 0 cell_8_129_0
    | exact certificate_sound 8 129 1 cell_8_129_1
    | exact certificate_sound 8 129 2 cell_8_129_2
    | exact certificate_sound 8 129 3 cell_8_129_3
    | exact certificate_sound 8 129 4 cell_8_129_4
    | exact certificate_sound 8 129 5 cell_8_129_5
theorem cell_8_130_0 : CertificateAt 8 130 0 := by decide +kernel
theorem cell_8_130_1 : CertificateAt 8 130 1 := by decide +kernel
theorem cell_8_130_2 : CertificateAt 8 130 2 := by decide +kernel
theorem cell_8_130_3 : CertificateAt 8 130 3 := by decide +kernel
theorem cell_8_130_4 : CertificateAt 8 130 4 := by decide +kernel
theorem cell_8_130_5 : CertificateAt 8 130 5 := by decide +kernel
theorem row_8_130 : ThresholdAt 8 130 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 130 0 cell_8_130_0
    | exact certificate_sound 8 130 1 cell_8_130_1
    | exact certificate_sound 8 130 2 cell_8_130_2
    | exact certificate_sound 8 130 3 cell_8_130_3
    | exact certificate_sound 8 130 4 cell_8_130_4
    | exact certificate_sound 8 130 5 cell_8_130_5
theorem cell_8_131_0 : CertificateAt 8 131 0 := by decide +kernel
theorem cell_8_131_1 : CertificateAt 8 131 1 := by decide +kernel
theorem cell_8_131_2 : CertificateAt 8 131 2 := by decide +kernel
theorem cell_8_131_3 : CertificateAt 8 131 3 := by decide +kernel
theorem cell_8_131_4 : CertificateAt 8 131 4 := by decide +kernel
theorem cell_8_131_5 : CertificateAt 8 131 5 := by decide +kernel
theorem row_8_131 : ThresholdAt 8 131 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 8 131 0 cell_8_131_0
    | exact certificate_sound 8 131 1 cell_8_131_1
    | exact certificate_sound 8 131 2 cell_8_131_2
    | exact certificate_sound 8 131 3 cell_8_131_3
    | exact certificate_sound 8 131 4 cell_8_131_4
    | exact certificate_sound 8 131 5 cell_8_131_5
theorem checkedR8 : ∀ V ∈ List.range 132, ThresholdAt 8 V := by
  intro V hV
  have hv : V < 132 := List.mem_range.mp hV
  by_cases h0_132 : V < 66
  · by_cases h0_66 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_8_0
              · have he : V = 1 := by omega
                subst V
                exact row_8_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_8_2
              · have he : V = 3 := by omega
                subst V
                exact row_8_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_8_4
              · have he : V = 5 := by omega
                subst V
                exact row_8_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_8_6
              · have he : V = 7 := by omega
                subst V
                exact row_8_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_8_8
              · have he : V = 9 := by omega
                subst V
                exact row_8_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_8_10
              · have he : V = 11 := by omega
                subst V
                exact row_8_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_8_12
              · have he : V = 13 := by omega
                subst V
                exact row_8_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_8_14
              · have he : V = 15 := by omega
                subst V
                exact row_8_15
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_8_16
              · have he : V = 17 := by omega
                subst V
                exact row_8_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_8_18
              · have he : V = 19 := by omega
                subst V
                exact row_8_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_8_20
              · have he : V = 21 := by omega
                subst V
                exact row_8_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_8_22
              · have he : V = 23 := by omega
                subst V
                exact row_8_23
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_8_24
              · have he : V = 25 := by omega
                subst V
                exact row_8_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_8_26
              · have he : V = 27 := by omega
                subst V
                exact row_8_27
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_8_28
              · have he : V = 29 := by omega
                subst V
                exact row_8_29
            · by_cases h30_33 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_8_30
              · by_cases h31_33 : V < 32
                · have he : V = 31 := by omega
                  subst V
                  exact row_8_31
                · have he : V = 32 := by omega
                  subst V
                  exact row_8_32
    · by_cases h33_66 : V < 49
      · by_cases h33_49 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_8_33
              · have he : V = 34 := by omega
                subst V
                exact row_8_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_8_35
              · have he : V = 36 := by omega
                subst V
                exact row_8_36
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_8_37
              · have he : V = 38 := by omega
                subst V
                exact row_8_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_8_39
              · have he : V = 40 := by omega
                subst V
                exact row_8_40
        · by_cases h41_49 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_8_41
              · have he : V = 42 := by omega
                subst V
                exact row_8_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_8_43
              · have he : V = 44 := by omega
                subst V
                exact row_8_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_8_45
              · have he : V = 46 := by omega
                subst V
                exact row_8_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_8_47
              · have he : V = 48 := by omega
                subst V
                exact row_8_48
      · by_cases h49_66 : V < 57
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_8_49
              · have he : V = 50 := by omega
                subst V
                exact row_8_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_8_51
              · have he : V = 52 := by omega
                subst V
                exact row_8_52
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_8_53
              · have he : V = 54 := by omega
                subst V
                exact row_8_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_8_55
              · have he : V = 56 := by omega
                subst V
                exact row_8_56
        · by_cases h57_66 : V < 61
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_8_57
              · have he : V = 58 := by omega
                subst V
                exact row_8_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_8_59
              · have he : V = 60 := by omega
                subst V
                exact row_8_60
          · by_cases h61_66 : V < 63
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_8_61
              · have he : V = 62 := by omega
                subst V
                exact row_8_62
            · by_cases h63_66 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_8_63
              · by_cases h64_66 : V < 65
                · have he : V = 64 := by omega
                  subst V
                  exact row_8_64
                · have he : V = 65 := by omega
                  subst V
                  exact row_8_65
  · by_cases h66_132 : V < 99
    · by_cases h66_99 : V < 82
      · by_cases h66_82 : V < 74
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_8_66
              · have he : V = 67 := by omega
                subst V
                exact row_8_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_8_68
              · have he : V = 69 := by omega
                subst V
                exact row_8_69
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_8_70
              · have he : V = 71 := by omega
                subst V
                exact row_8_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_8_72
              · have he : V = 73 := by omega
                subst V
                exact row_8_73
        · by_cases h74_82 : V < 78
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_8_74
              · have he : V = 75 := by omega
                subst V
                exact row_8_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_8_76
              · have he : V = 77 := by omega
                subst V
                exact row_8_77
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_8_78
              · have he : V = 79 := by omega
                subst V
                exact row_8_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_8_80
              · have he : V = 81 := by omega
                subst V
                exact row_8_81
      · by_cases h82_99 : V < 90
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_8_82
              · have he : V = 83 := by omega
                subst V
                exact row_8_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_8_84
              · have he : V = 85 := by omega
                subst V
                exact row_8_85
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_8_86
              · have he : V = 87 := by omega
                subst V
                exact row_8_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_8_88
              · have he : V = 89 := by omega
                subst V
                exact row_8_89
        · by_cases h90_99 : V < 94
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_8_90
              · have he : V = 91 := by omega
                subst V
                exact row_8_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_8_92
              · have he : V = 93 := by omega
                subst V
                exact row_8_93
          · by_cases h94_99 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_8_94
              · have he : V = 95 := by omega
                subst V
                exact row_8_95
            · by_cases h96_99 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_8_96
              · by_cases h97_99 : V < 98
                · have he : V = 97 := by omega
                  subst V
                  exact row_8_97
                · have he : V = 98 := by omega
                  subst V
                  exact row_8_98
    · by_cases h99_132 : V < 115
      · by_cases h99_115 : V < 107
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_8_99
              · have he : V = 100 := by omega
                subst V
                exact row_8_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_8_101
              · have he : V = 102 := by omega
                subst V
                exact row_8_102
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_8_103
              · have he : V = 104 := by omega
                subst V
                exact row_8_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_8_105
              · have he : V = 106 := by omega
                subst V
                exact row_8_106
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_8_107
              · have he : V = 108 := by omega
                subst V
                exact row_8_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_8_109
              · have he : V = 110 := by omega
                subst V
                exact row_8_110
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_8_111
              · have he : V = 112 := by omega
                subst V
                exact row_8_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_8_113
              · have he : V = 114 := by omega
                subst V
                exact row_8_114
      · by_cases h115_132 : V < 123
        · by_cases h115_123 : V < 119
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_8_115
              · have he : V = 116 := by omega
                subst V
                exact row_8_116
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_8_117
              · have he : V = 118 := by omega
                subst V
                exact row_8_118
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_8_119
              · have he : V = 120 := by omega
                subst V
                exact row_8_120
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_8_121
              · have he : V = 122 := by omega
                subst V
                exact row_8_122
        · by_cases h123_132 : V < 127
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_8_123
              · have he : V = 124 := by omega
                subst V
                exact row_8_124
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_8_125
              · have he : V = 126 := by omega
                subst V
                exact row_8_126
          · by_cases h127_132 : V < 129
            · by_cases h127_129 : V < 128
              · have he : V = 127 := by omega
                subst V
                exact row_8_127
              · have he : V = 128 := by omega
                subst V
                exact row_8_128
            · by_cases h129_132 : V < 130
              · have he : V = 129 := by omega
                subst V
                exact row_8_129
              · by_cases h130_132 : V < 131
                · have he : V = 130 := by omega
                  subst V
                  exact row_8_130
                · have he : V = 131 := by omega
                  subst V
                  exact row_8_131
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
