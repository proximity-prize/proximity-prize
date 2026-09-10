import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked09

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_10_0_0 : CertificateAt 10 0 0 := by decide +kernel
theorem cell_10_0_1 : CertificateAt 10 0 1 := by decide +kernel
theorem cell_10_0_2 : CertificateAt 10 0 2 := by decide +kernel
theorem cell_10_0_3 : CertificateAt 10 0 3 := by decide +kernel
theorem cell_10_0_4 : CertificateAt 10 0 4 := by decide +kernel
theorem cell_10_0_5 : CertificateAt 10 0 5 := by decide +kernel
theorem row_10_0 : ThresholdAt 10 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 0 0 cell_10_0_0
    | exact certificate_sound 10 0 1 cell_10_0_1
    | exact certificate_sound 10 0 2 cell_10_0_2
    | exact certificate_sound 10 0 3 cell_10_0_3
    | exact certificate_sound 10 0 4 cell_10_0_4
    | exact certificate_sound 10 0 5 cell_10_0_5
theorem cell_10_1_0 : CertificateAt 10 1 0 := by decide +kernel
theorem cell_10_1_1 : CertificateAt 10 1 1 := by decide +kernel
theorem cell_10_1_2 : CertificateAt 10 1 2 := by decide +kernel
theorem cell_10_1_3 : CertificateAt 10 1 3 := by decide +kernel
theorem cell_10_1_4 : CertificateAt 10 1 4 := by decide +kernel
theorem cell_10_1_5 : CertificateAt 10 1 5 := by decide +kernel
theorem row_10_1 : ThresholdAt 10 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 1 0 cell_10_1_0
    | exact certificate_sound 10 1 1 cell_10_1_1
    | exact certificate_sound 10 1 2 cell_10_1_2
    | exact certificate_sound 10 1 3 cell_10_1_3
    | exact certificate_sound 10 1 4 cell_10_1_4
    | exact certificate_sound 10 1 5 cell_10_1_5
theorem cell_10_2_0 : CertificateAt 10 2 0 := by decide +kernel
theorem cell_10_2_1 : CertificateAt 10 2 1 := by decide +kernel
theorem cell_10_2_2 : CertificateAt 10 2 2 := by decide +kernel
theorem cell_10_2_3 : CertificateAt 10 2 3 := by decide +kernel
theorem cell_10_2_4 : CertificateAt 10 2 4 := by decide +kernel
theorem cell_10_2_5 : CertificateAt 10 2 5 := by decide +kernel
theorem row_10_2 : ThresholdAt 10 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 2 0 cell_10_2_0
    | exact certificate_sound 10 2 1 cell_10_2_1
    | exact certificate_sound 10 2 2 cell_10_2_2
    | exact certificate_sound 10 2 3 cell_10_2_3
    | exact certificate_sound 10 2 4 cell_10_2_4
    | exact certificate_sound 10 2 5 cell_10_2_5
theorem cell_10_3_0 : CertificateAt 10 3 0 := by decide +kernel
theorem cell_10_3_1 : CertificateAt 10 3 1 := by decide +kernel
theorem cell_10_3_2 : CertificateAt 10 3 2 := by decide +kernel
theorem cell_10_3_3 : CertificateAt 10 3 3 := by decide +kernel
theorem cell_10_3_4 : CertificateAt 10 3 4 := by decide +kernel
theorem cell_10_3_5 : CertificateAt 10 3 5 := by decide +kernel
theorem row_10_3 : ThresholdAt 10 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 3 0 cell_10_3_0
    | exact certificate_sound 10 3 1 cell_10_3_1
    | exact certificate_sound 10 3 2 cell_10_3_2
    | exact certificate_sound 10 3 3 cell_10_3_3
    | exact certificate_sound 10 3 4 cell_10_3_4
    | exact certificate_sound 10 3 5 cell_10_3_5
theorem cell_10_4_0 : CertificateAt 10 4 0 := by decide +kernel
theorem cell_10_4_1 : CertificateAt 10 4 1 := by decide +kernel
theorem cell_10_4_2 : CertificateAt 10 4 2 := by decide +kernel
theorem cell_10_4_3 : CertificateAt 10 4 3 := by decide +kernel
theorem cell_10_4_4 : CertificateAt 10 4 4 := by decide +kernel
theorem cell_10_4_5 : CertificateAt 10 4 5 := by decide +kernel
theorem row_10_4 : ThresholdAt 10 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 4 0 cell_10_4_0
    | exact certificate_sound 10 4 1 cell_10_4_1
    | exact certificate_sound 10 4 2 cell_10_4_2
    | exact certificate_sound 10 4 3 cell_10_4_3
    | exact certificate_sound 10 4 4 cell_10_4_4
    | exact certificate_sound 10 4 5 cell_10_4_5
theorem cell_10_5_0 : CertificateAt 10 5 0 := by decide +kernel
theorem cell_10_5_1 : CertificateAt 10 5 1 := by decide +kernel
theorem cell_10_5_2 : CertificateAt 10 5 2 := by decide +kernel
theorem cell_10_5_3 : CertificateAt 10 5 3 := by decide +kernel
theorem cell_10_5_4 : CertificateAt 10 5 4 := by decide +kernel
theorem cell_10_5_5 : CertificateAt 10 5 5 := by decide +kernel
theorem row_10_5 : ThresholdAt 10 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 5 0 cell_10_5_0
    | exact certificate_sound 10 5 1 cell_10_5_1
    | exact certificate_sound 10 5 2 cell_10_5_2
    | exact certificate_sound 10 5 3 cell_10_5_3
    | exact certificate_sound 10 5 4 cell_10_5_4
    | exact certificate_sound 10 5 5 cell_10_5_5
theorem cell_10_6_0 : CertificateAt 10 6 0 := by decide +kernel
theorem cell_10_6_1 : CertificateAt 10 6 1 := by decide +kernel
theorem cell_10_6_2 : CertificateAt 10 6 2 := by decide +kernel
theorem cell_10_6_3 : CertificateAt 10 6 3 := by decide +kernel
theorem cell_10_6_4 : CertificateAt 10 6 4 := by decide +kernel
theorem cell_10_6_5 : CertificateAt 10 6 5 := by decide +kernel
theorem row_10_6 : ThresholdAt 10 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 6 0 cell_10_6_0
    | exact certificate_sound 10 6 1 cell_10_6_1
    | exact certificate_sound 10 6 2 cell_10_6_2
    | exact certificate_sound 10 6 3 cell_10_6_3
    | exact certificate_sound 10 6 4 cell_10_6_4
    | exact certificate_sound 10 6 5 cell_10_6_5
theorem cell_10_7_0 : CertificateAt 10 7 0 := by decide +kernel
theorem cell_10_7_1 : CertificateAt 10 7 1 := by decide +kernel
theorem cell_10_7_2 : CertificateAt 10 7 2 := by decide +kernel
theorem cell_10_7_3 : CertificateAt 10 7 3 := by decide +kernel
theorem cell_10_7_4 : CertificateAt 10 7 4 := by decide +kernel
theorem cell_10_7_5 : CertificateAt 10 7 5 := by decide +kernel
theorem row_10_7 : ThresholdAt 10 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 7 0 cell_10_7_0
    | exact certificate_sound 10 7 1 cell_10_7_1
    | exact certificate_sound 10 7 2 cell_10_7_2
    | exact certificate_sound 10 7 3 cell_10_7_3
    | exact certificate_sound 10 7 4 cell_10_7_4
    | exact certificate_sound 10 7 5 cell_10_7_5
theorem cell_10_8_0 : CertificateAt 10 8 0 := by decide +kernel
theorem cell_10_8_1 : CertificateAt 10 8 1 := by decide +kernel
theorem cell_10_8_2 : CertificateAt 10 8 2 := by decide +kernel
theorem cell_10_8_3 : CertificateAt 10 8 3 := by decide +kernel
theorem cell_10_8_4 : CertificateAt 10 8 4 := by decide +kernel
theorem cell_10_8_5 : CertificateAt 10 8 5 := by decide +kernel
theorem row_10_8 : ThresholdAt 10 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 8 0 cell_10_8_0
    | exact certificate_sound 10 8 1 cell_10_8_1
    | exact certificate_sound 10 8 2 cell_10_8_2
    | exact certificate_sound 10 8 3 cell_10_8_3
    | exact certificate_sound 10 8 4 cell_10_8_4
    | exact certificate_sound 10 8 5 cell_10_8_5
theorem cell_10_9_0 : CertificateAt 10 9 0 := by decide +kernel
theorem cell_10_9_1 : CertificateAt 10 9 1 := by decide +kernel
theorem cell_10_9_2 : CertificateAt 10 9 2 := by decide +kernel
theorem cell_10_9_3 : CertificateAt 10 9 3 := by decide +kernel
theorem cell_10_9_4 : CertificateAt 10 9 4 := by decide +kernel
theorem cell_10_9_5 : CertificateAt 10 9 5 := by decide +kernel
theorem row_10_9 : ThresholdAt 10 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 9 0 cell_10_9_0
    | exact certificate_sound 10 9 1 cell_10_9_1
    | exact certificate_sound 10 9 2 cell_10_9_2
    | exact certificate_sound 10 9 3 cell_10_9_3
    | exact certificate_sound 10 9 4 cell_10_9_4
    | exact certificate_sound 10 9 5 cell_10_9_5
theorem cell_10_10_0 : CertificateAt 10 10 0 := by decide +kernel
theorem cell_10_10_1 : CertificateAt 10 10 1 := by decide +kernel
theorem cell_10_10_2 : CertificateAt 10 10 2 := by decide +kernel
theorem cell_10_10_3 : CertificateAt 10 10 3 := by decide +kernel
theorem cell_10_10_4 : CertificateAt 10 10 4 := by decide +kernel
theorem cell_10_10_5 : CertificateAt 10 10 5 := by decide +kernel
theorem row_10_10 : ThresholdAt 10 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 10 0 cell_10_10_0
    | exact certificate_sound 10 10 1 cell_10_10_1
    | exact certificate_sound 10 10 2 cell_10_10_2
    | exact certificate_sound 10 10 3 cell_10_10_3
    | exact certificate_sound 10 10 4 cell_10_10_4
    | exact certificate_sound 10 10 5 cell_10_10_5
theorem cell_10_11_0 : CertificateAt 10 11 0 := by decide +kernel
theorem cell_10_11_1 : CertificateAt 10 11 1 := by decide +kernel
theorem cell_10_11_2 : CertificateAt 10 11 2 := by decide +kernel
theorem cell_10_11_3 : CertificateAt 10 11 3 := by decide +kernel
theorem cell_10_11_4 : CertificateAt 10 11 4 := by decide +kernel
theorem cell_10_11_5 : CertificateAt 10 11 5 := by decide +kernel
theorem row_10_11 : ThresholdAt 10 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 11 0 cell_10_11_0
    | exact certificate_sound 10 11 1 cell_10_11_1
    | exact certificate_sound 10 11 2 cell_10_11_2
    | exact certificate_sound 10 11 3 cell_10_11_3
    | exact certificate_sound 10 11 4 cell_10_11_4
    | exact certificate_sound 10 11 5 cell_10_11_5
theorem cell_10_12_0 : CertificateAt 10 12 0 := by decide +kernel
theorem cell_10_12_1 : CertificateAt 10 12 1 := by decide +kernel
theorem cell_10_12_2 : CertificateAt 10 12 2 := by decide +kernel
theorem cell_10_12_3 : CertificateAt 10 12 3 := by decide +kernel
theorem cell_10_12_4 : CertificateAt 10 12 4 := by decide +kernel
theorem cell_10_12_5 : CertificateAt 10 12 5 := by decide +kernel
theorem row_10_12 : ThresholdAt 10 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 12 0 cell_10_12_0
    | exact certificate_sound 10 12 1 cell_10_12_1
    | exact certificate_sound 10 12 2 cell_10_12_2
    | exact certificate_sound 10 12 3 cell_10_12_3
    | exact certificate_sound 10 12 4 cell_10_12_4
    | exact certificate_sound 10 12 5 cell_10_12_5
theorem cell_10_13_0 : CertificateAt 10 13 0 := by decide +kernel
theorem cell_10_13_1 : CertificateAt 10 13 1 := by decide +kernel
theorem cell_10_13_2 : CertificateAt 10 13 2 := by decide +kernel
theorem cell_10_13_3 : CertificateAt 10 13 3 := by decide +kernel
theorem cell_10_13_4 : CertificateAt 10 13 4 := by decide +kernel
theorem cell_10_13_5 : CertificateAt 10 13 5 := by decide +kernel
theorem row_10_13 : ThresholdAt 10 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 13 0 cell_10_13_0
    | exact certificate_sound 10 13 1 cell_10_13_1
    | exact certificate_sound 10 13 2 cell_10_13_2
    | exact certificate_sound 10 13 3 cell_10_13_3
    | exact certificate_sound 10 13 4 cell_10_13_4
    | exact certificate_sound 10 13 5 cell_10_13_5
theorem cell_10_14_0 : CertificateAt 10 14 0 := by decide +kernel
theorem cell_10_14_1 : CertificateAt 10 14 1 := by decide +kernel
theorem cell_10_14_2 : CertificateAt 10 14 2 := by decide +kernel
theorem cell_10_14_3 : CertificateAt 10 14 3 := by decide +kernel
theorem cell_10_14_4 : CertificateAt 10 14 4 := by decide +kernel
theorem cell_10_14_5 : CertificateAt 10 14 5 := by decide +kernel
theorem row_10_14 : ThresholdAt 10 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 14 0 cell_10_14_0
    | exact certificate_sound 10 14 1 cell_10_14_1
    | exact certificate_sound 10 14 2 cell_10_14_2
    | exact certificate_sound 10 14 3 cell_10_14_3
    | exact certificate_sound 10 14 4 cell_10_14_4
    | exact certificate_sound 10 14 5 cell_10_14_5
theorem cell_10_15_0 : CertificateAt 10 15 0 := by decide +kernel
theorem cell_10_15_1 : CertificateAt 10 15 1 := by decide +kernel
theorem cell_10_15_2 : CertificateAt 10 15 2 := by decide +kernel
theorem cell_10_15_3 : CertificateAt 10 15 3 := by decide +kernel
theorem cell_10_15_4 : CertificateAt 10 15 4 := by decide +kernel
theorem cell_10_15_5 : CertificateAt 10 15 5 := by decide +kernel
theorem row_10_15 : ThresholdAt 10 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 15 0 cell_10_15_0
    | exact certificate_sound 10 15 1 cell_10_15_1
    | exact certificate_sound 10 15 2 cell_10_15_2
    | exact certificate_sound 10 15 3 cell_10_15_3
    | exact certificate_sound 10 15 4 cell_10_15_4
    | exact certificate_sound 10 15 5 cell_10_15_5
theorem cell_10_16_0 : CertificateAt 10 16 0 := by decide +kernel
theorem cell_10_16_1 : CertificateAt 10 16 1 := by decide +kernel
theorem cell_10_16_2 : CertificateAt 10 16 2 := by decide +kernel
theorem cell_10_16_3 : CertificateAt 10 16 3 := by decide +kernel
theorem cell_10_16_4 : CertificateAt 10 16 4 := by decide +kernel
theorem cell_10_16_5 : CertificateAt 10 16 5 := by decide +kernel
theorem row_10_16 : ThresholdAt 10 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 16 0 cell_10_16_0
    | exact certificate_sound 10 16 1 cell_10_16_1
    | exact certificate_sound 10 16 2 cell_10_16_2
    | exact certificate_sound 10 16 3 cell_10_16_3
    | exact certificate_sound 10 16 4 cell_10_16_4
    | exact certificate_sound 10 16 5 cell_10_16_5
theorem cell_10_17_0 : CertificateAt 10 17 0 := by decide +kernel
theorem cell_10_17_1 : CertificateAt 10 17 1 := by decide +kernel
theorem cell_10_17_2 : CertificateAt 10 17 2 := by decide +kernel
theorem cell_10_17_3 : CertificateAt 10 17 3 := by decide +kernel
theorem cell_10_17_4 : CertificateAt 10 17 4 := by decide +kernel
theorem cell_10_17_5 : CertificateAt 10 17 5 := by decide +kernel
theorem row_10_17 : ThresholdAt 10 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 17 0 cell_10_17_0
    | exact certificate_sound 10 17 1 cell_10_17_1
    | exact certificate_sound 10 17 2 cell_10_17_2
    | exact certificate_sound 10 17 3 cell_10_17_3
    | exact certificate_sound 10 17 4 cell_10_17_4
    | exact certificate_sound 10 17 5 cell_10_17_5
theorem cell_10_18_0 : CertificateAt 10 18 0 := by decide +kernel
theorem cell_10_18_1 : CertificateAt 10 18 1 := by decide +kernel
theorem cell_10_18_2 : CertificateAt 10 18 2 := by decide +kernel
theorem cell_10_18_3 : CertificateAt 10 18 3 := by decide +kernel
theorem cell_10_18_4 : CertificateAt 10 18 4 := by decide +kernel
theorem cell_10_18_5 : CertificateAt 10 18 5 := by decide +kernel
theorem row_10_18 : ThresholdAt 10 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 18 0 cell_10_18_0
    | exact certificate_sound 10 18 1 cell_10_18_1
    | exact certificate_sound 10 18 2 cell_10_18_2
    | exact certificate_sound 10 18 3 cell_10_18_3
    | exact certificate_sound 10 18 4 cell_10_18_4
    | exact certificate_sound 10 18 5 cell_10_18_5
theorem cell_10_19_0 : CertificateAt 10 19 0 := by decide +kernel
theorem cell_10_19_1 : CertificateAt 10 19 1 := by decide +kernel
theorem cell_10_19_2 : CertificateAt 10 19 2 := by decide +kernel
theorem cell_10_19_3 : CertificateAt 10 19 3 := by decide +kernel
theorem cell_10_19_4 : CertificateAt 10 19 4 := by decide +kernel
theorem cell_10_19_5 : CertificateAt 10 19 5 := by decide +kernel
theorem row_10_19 : ThresholdAt 10 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 19 0 cell_10_19_0
    | exact certificate_sound 10 19 1 cell_10_19_1
    | exact certificate_sound 10 19 2 cell_10_19_2
    | exact certificate_sound 10 19 3 cell_10_19_3
    | exact certificate_sound 10 19 4 cell_10_19_4
    | exact certificate_sound 10 19 5 cell_10_19_5
theorem cell_10_20_0 : CertificateAt 10 20 0 := by decide +kernel
theorem cell_10_20_1 : CertificateAt 10 20 1 := by decide +kernel
theorem cell_10_20_2 : CertificateAt 10 20 2 := by decide +kernel
theorem cell_10_20_3 : CertificateAt 10 20 3 := by decide +kernel
theorem cell_10_20_4 : CertificateAt 10 20 4 := by decide +kernel
theorem cell_10_20_5 : CertificateAt 10 20 5 := by decide +kernel
theorem row_10_20 : ThresholdAt 10 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 20 0 cell_10_20_0
    | exact certificate_sound 10 20 1 cell_10_20_1
    | exact certificate_sound 10 20 2 cell_10_20_2
    | exact certificate_sound 10 20 3 cell_10_20_3
    | exact certificate_sound 10 20 4 cell_10_20_4
    | exact certificate_sound 10 20 5 cell_10_20_5
theorem cell_10_21_0 : CertificateAt 10 21 0 := by decide +kernel
theorem cell_10_21_1 : CertificateAt 10 21 1 := by decide +kernel
theorem cell_10_21_2 : CertificateAt 10 21 2 := by decide +kernel
theorem cell_10_21_3 : CertificateAt 10 21 3 := by decide +kernel
theorem cell_10_21_4 : CertificateAt 10 21 4 := by decide +kernel
theorem cell_10_21_5 : CertificateAt 10 21 5 := by decide +kernel
theorem row_10_21 : ThresholdAt 10 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 21 0 cell_10_21_0
    | exact certificate_sound 10 21 1 cell_10_21_1
    | exact certificate_sound 10 21 2 cell_10_21_2
    | exact certificate_sound 10 21 3 cell_10_21_3
    | exact certificate_sound 10 21 4 cell_10_21_4
    | exact certificate_sound 10 21 5 cell_10_21_5
theorem cell_10_22_0 : CertificateAt 10 22 0 := by decide +kernel
theorem cell_10_22_1 : CertificateAt 10 22 1 := by decide +kernel
theorem cell_10_22_2 : CertificateAt 10 22 2 := by decide +kernel
theorem cell_10_22_3 : CertificateAt 10 22 3 := by decide +kernel
theorem cell_10_22_4 : CertificateAt 10 22 4 := by decide +kernel
theorem cell_10_22_5 : CertificateAt 10 22 5 := by decide +kernel
theorem row_10_22 : ThresholdAt 10 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 22 0 cell_10_22_0
    | exact certificate_sound 10 22 1 cell_10_22_1
    | exact certificate_sound 10 22 2 cell_10_22_2
    | exact certificate_sound 10 22 3 cell_10_22_3
    | exact certificate_sound 10 22 4 cell_10_22_4
    | exact certificate_sound 10 22 5 cell_10_22_5
theorem cell_10_23_0 : CertificateAt 10 23 0 := by decide +kernel
theorem cell_10_23_1 : CertificateAt 10 23 1 := by decide +kernel
theorem cell_10_23_2 : CertificateAt 10 23 2 := by decide +kernel
theorem cell_10_23_3 : CertificateAt 10 23 3 := by decide +kernel
theorem cell_10_23_4 : CertificateAt 10 23 4 := by decide +kernel
theorem cell_10_23_5 : CertificateAt 10 23 5 := by decide +kernel
theorem row_10_23 : ThresholdAt 10 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 23 0 cell_10_23_0
    | exact certificate_sound 10 23 1 cell_10_23_1
    | exact certificate_sound 10 23 2 cell_10_23_2
    | exact certificate_sound 10 23 3 cell_10_23_3
    | exact certificate_sound 10 23 4 cell_10_23_4
    | exact certificate_sound 10 23 5 cell_10_23_5
theorem cell_10_24_0 : CertificateAt 10 24 0 := by decide +kernel
theorem cell_10_24_1 : CertificateAt 10 24 1 := by decide +kernel
theorem cell_10_24_2 : CertificateAt 10 24 2 := by decide +kernel
theorem cell_10_24_3 : CertificateAt 10 24 3 := by decide +kernel
theorem cell_10_24_4 : CertificateAt 10 24 4 := by decide +kernel
theorem cell_10_24_5 : CertificateAt 10 24 5 := by decide +kernel
theorem row_10_24 : ThresholdAt 10 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 24 0 cell_10_24_0
    | exact certificate_sound 10 24 1 cell_10_24_1
    | exact certificate_sound 10 24 2 cell_10_24_2
    | exact certificate_sound 10 24 3 cell_10_24_3
    | exact certificate_sound 10 24 4 cell_10_24_4
    | exact certificate_sound 10 24 5 cell_10_24_5
theorem cell_10_25_0 : CertificateAt 10 25 0 := by decide +kernel
theorem cell_10_25_1 : CertificateAt 10 25 1 := by decide +kernel
theorem cell_10_25_2 : CertificateAt 10 25 2 := by decide +kernel
theorem cell_10_25_3 : CertificateAt 10 25 3 := by decide +kernel
theorem cell_10_25_4 : CertificateAt 10 25 4 := by decide +kernel
theorem cell_10_25_5 : CertificateAt 10 25 5 := by decide +kernel
theorem row_10_25 : ThresholdAt 10 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 25 0 cell_10_25_0
    | exact certificate_sound 10 25 1 cell_10_25_1
    | exact certificate_sound 10 25 2 cell_10_25_2
    | exact certificate_sound 10 25 3 cell_10_25_3
    | exact certificate_sound 10 25 4 cell_10_25_4
    | exact certificate_sound 10 25 5 cell_10_25_5
theorem cell_10_26_0 : CertificateAt 10 26 0 := by decide +kernel
theorem cell_10_26_1 : CertificateAt 10 26 1 := by decide +kernel
theorem cell_10_26_2 : CertificateAt 10 26 2 := by decide +kernel
theorem cell_10_26_3 : CertificateAt 10 26 3 := by decide +kernel
theorem cell_10_26_4 : CertificateAt 10 26 4 := by decide +kernel
theorem cell_10_26_5 : CertificateAt 10 26 5 := by decide +kernel
theorem row_10_26 : ThresholdAt 10 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 26 0 cell_10_26_0
    | exact certificate_sound 10 26 1 cell_10_26_1
    | exact certificate_sound 10 26 2 cell_10_26_2
    | exact certificate_sound 10 26 3 cell_10_26_3
    | exact certificate_sound 10 26 4 cell_10_26_4
    | exact certificate_sound 10 26 5 cell_10_26_5
theorem cell_10_27_0 : CertificateAt 10 27 0 := by decide +kernel
theorem cell_10_27_1 : CertificateAt 10 27 1 := by decide +kernel
theorem cell_10_27_2 : CertificateAt 10 27 2 := by decide +kernel
theorem cell_10_27_3 : CertificateAt 10 27 3 := by decide +kernel
theorem cell_10_27_4 : CertificateAt 10 27 4 := by decide +kernel
theorem cell_10_27_5 : CertificateAt 10 27 5 := by decide +kernel
theorem row_10_27 : ThresholdAt 10 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 27 0 cell_10_27_0
    | exact certificate_sound 10 27 1 cell_10_27_1
    | exact certificate_sound 10 27 2 cell_10_27_2
    | exact certificate_sound 10 27 3 cell_10_27_3
    | exact certificate_sound 10 27 4 cell_10_27_4
    | exact certificate_sound 10 27 5 cell_10_27_5
theorem cell_10_28_0 : CertificateAt 10 28 0 := by decide +kernel
theorem cell_10_28_1 : CertificateAt 10 28 1 := by decide +kernel
theorem cell_10_28_2 : CertificateAt 10 28 2 := by decide +kernel
theorem cell_10_28_3 : CertificateAt 10 28 3 := by decide +kernel
theorem cell_10_28_4 : CertificateAt 10 28 4 := by decide +kernel
theorem cell_10_28_5 : CertificateAt 10 28 5 := by decide +kernel
theorem row_10_28 : ThresholdAt 10 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 28 0 cell_10_28_0
    | exact certificate_sound 10 28 1 cell_10_28_1
    | exact certificate_sound 10 28 2 cell_10_28_2
    | exact certificate_sound 10 28 3 cell_10_28_3
    | exact certificate_sound 10 28 4 cell_10_28_4
    | exact certificate_sound 10 28 5 cell_10_28_5
theorem cell_10_29_0 : CertificateAt 10 29 0 := by decide +kernel
theorem cell_10_29_1 : CertificateAt 10 29 1 := by decide +kernel
theorem cell_10_29_2 : CertificateAt 10 29 2 := by decide +kernel
theorem cell_10_29_3 : CertificateAt 10 29 3 := by decide +kernel
theorem cell_10_29_4 : CertificateAt 10 29 4 := by decide +kernel
theorem cell_10_29_5 : CertificateAt 10 29 5 := by decide +kernel
theorem row_10_29 : ThresholdAt 10 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 29 0 cell_10_29_0
    | exact certificate_sound 10 29 1 cell_10_29_1
    | exact certificate_sound 10 29 2 cell_10_29_2
    | exact certificate_sound 10 29 3 cell_10_29_3
    | exact certificate_sound 10 29 4 cell_10_29_4
    | exact certificate_sound 10 29 5 cell_10_29_5
theorem cell_10_30_0 : CertificateAt 10 30 0 := by decide +kernel
theorem cell_10_30_1 : CertificateAt 10 30 1 := by decide +kernel
theorem cell_10_30_2 : CertificateAt 10 30 2 := by decide +kernel
theorem cell_10_30_3 : CertificateAt 10 30 3 := by decide +kernel
theorem cell_10_30_4 : CertificateAt 10 30 4 := by decide +kernel
theorem cell_10_30_5 : CertificateAt 10 30 5 := by decide +kernel
theorem row_10_30 : ThresholdAt 10 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 30 0 cell_10_30_0
    | exact certificate_sound 10 30 1 cell_10_30_1
    | exact certificate_sound 10 30 2 cell_10_30_2
    | exact certificate_sound 10 30 3 cell_10_30_3
    | exact certificate_sound 10 30 4 cell_10_30_4
    | exact certificate_sound 10 30 5 cell_10_30_5
theorem cell_10_31_0 : CertificateAt 10 31 0 := by decide +kernel
theorem cell_10_31_1 : CertificateAt 10 31 1 := by decide +kernel
theorem cell_10_31_2 : CertificateAt 10 31 2 := by decide +kernel
theorem cell_10_31_3 : CertificateAt 10 31 3 := by decide +kernel
theorem cell_10_31_4 : CertificateAt 10 31 4 := by decide +kernel
theorem cell_10_31_5 : CertificateAt 10 31 5 := by decide +kernel
theorem row_10_31 : ThresholdAt 10 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 31 0 cell_10_31_0
    | exact certificate_sound 10 31 1 cell_10_31_1
    | exact certificate_sound 10 31 2 cell_10_31_2
    | exact certificate_sound 10 31 3 cell_10_31_3
    | exact certificate_sound 10 31 4 cell_10_31_4
    | exact certificate_sound 10 31 5 cell_10_31_5
theorem cell_10_32_0 : CertificateAt 10 32 0 := by decide +kernel
theorem cell_10_32_1 : CertificateAt 10 32 1 := by decide +kernel
theorem cell_10_32_2 : CertificateAt 10 32 2 := by decide +kernel
theorem cell_10_32_3 : CertificateAt 10 32 3 := by decide +kernel
theorem cell_10_32_4 : CertificateAt 10 32 4 := by decide +kernel
theorem cell_10_32_5 : CertificateAt 10 32 5 := by decide +kernel
theorem row_10_32 : ThresholdAt 10 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 32 0 cell_10_32_0
    | exact certificate_sound 10 32 1 cell_10_32_1
    | exact certificate_sound 10 32 2 cell_10_32_2
    | exact certificate_sound 10 32 3 cell_10_32_3
    | exact certificate_sound 10 32 4 cell_10_32_4
    | exact certificate_sound 10 32 5 cell_10_32_5
theorem cell_10_33_0 : CertificateAt 10 33 0 := by decide +kernel
theorem cell_10_33_1 : CertificateAt 10 33 1 := by decide +kernel
theorem cell_10_33_2 : CertificateAt 10 33 2 := by decide +kernel
theorem cell_10_33_3 : CertificateAt 10 33 3 := by decide +kernel
theorem cell_10_33_4 : CertificateAt 10 33 4 := by decide +kernel
theorem cell_10_33_5 : CertificateAt 10 33 5 := by decide +kernel
theorem row_10_33 : ThresholdAt 10 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 33 0 cell_10_33_0
    | exact certificate_sound 10 33 1 cell_10_33_1
    | exact certificate_sound 10 33 2 cell_10_33_2
    | exact certificate_sound 10 33 3 cell_10_33_3
    | exact certificate_sound 10 33 4 cell_10_33_4
    | exact certificate_sound 10 33 5 cell_10_33_5
theorem cell_10_34_0 : CertificateAt 10 34 0 := by decide +kernel
theorem cell_10_34_1 : CertificateAt 10 34 1 := by decide +kernel
theorem cell_10_34_2 : CertificateAt 10 34 2 := by decide +kernel
theorem cell_10_34_3 : CertificateAt 10 34 3 := by decide +kernel
theorem cell_10_34_4 : CertificateAt 10 34 4 := by decide +kernel
theorem cell_10_34_5 : CertificateAt 10 34 5 := by decide +kernel
theorem row_10_34 : ThresholdAt 10 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 34 0 cell_10_34_0
    | exact certificate_sound 10 34 1 cell_10_34_1
    | exact certificate_sound 10 34 2 cell_10_34_2
    | exact certificate_sound 10 34 3 cell_10_34_3
    | exact certificate_sound 10 34 4 cell_10_34_4
    | exact certificate_sound 10 34 5 cell_10_34_5
theorem cell_10_35_0 : CertificateAt 10 35 0 := by decide +kernel
theorem cell_10_35_1 : CertificateAt 10 35 1 := by decide +kernel
theorem cell_10_35_2 : CertificateAt 10 35 2 := by decide +kernel
theorem cell_10_35_3 : CertificateAt 10 35 3 := by decide +kernel
theorem cell_10_35_4 : CertificateAt 10 35 4 := by decide +kernel
theorem cell_10_35_5 : CertificateAt 10 35 5 := by decide +kernel
theorem row_10_35 : ThresholdAt 10 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 35 0 cell_10_35_0
    | exact certificate_sound 10 35 1 cell_10_35_1
    | exact certificate_sound 10 35 2 cell_10_35_2
    | exact certificate_sound 10 35 3 cell_10_35_3
    | exact certificate_sound 10 35 4 cell_10_35_4
    | exact certificate_sound 10 35 5 cell_10_35_5
theorem cell_10_36_0 : CertificateAt 10 36 0 := by decide +kernel
theorem cell_10_36_1 : CertificateAt 10 36 1 := by decide +kernel
theorem cell_10_36_2 : CertificateAt 10 36 2 := by decide +kernel
theorem cell_10_36_3 : CertificateAt 10 36 3 := by decide +kernel
theorem cell_10_36_4 : CertificateAt 10 36 4 := by decide +kernel
theorem cell_10_36_5 : CertificateAt 10 36 5 := by decide +kernel
theorem row_10_36 : ThresholdAt 10 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 36 0 cell_10_36_0
    | exact certificate_sound 10 36 1 cell_10_36_1
    | exact certificate_sound 10 36 2 cell_10_36_2
    | exact certificate_sound 10 36 3 cell_10_36_3
    | exact certificate_sound 10 36 4 cell_10_36_4
    | exact certificate_sound 10 36 5 cell_10_36_5
theorem cell_10_37_0 : CertificateAt 10 37 0 := by decide +kernel
theorem cell_10_37_1 : CertificateAt 10 37 1 := by decide +kernel
theorem cell_10_37_2 : CertificateAt 10 37 2 := by decide +kernel
theorem cell_10_37_3 : CertificateAt 10 37 3 := by decide +kernel
theorem cell_10_37_4 : CertificateAt 10 37 4 := by decide +kernel
theorem cell_10_37_5 : CertificateAt 10 37 5 := by decide +kernel
theorem row_10_37 : ThresholdAt 10 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 37 0 cell_10_37_0
    | exact certificate_sound 10 37 1 cell_10_37_1
    | exact certificate_sound 10 37 2 cell_10_37_2
    | exact certificate_sound 10 37 3 cell_10_37_3
    | exact certificate_sound 10 37 4 cell_10_37_4
    | exact certificate_sound 10 37 5 cell_10_37_5
theorem cell_10_38_0 : CertificateAt 10 38 0 := by decide +kernel
theorem cell_10_38_1 : CertificateAt 10 38 1 := by decide +kernel
theorem cell_10_38_2 : CertificateAt 10 38 2 := by decide +kernel
theorem cell_10_38_3 : CertificateAt 10 38 3 := by decide +kernel
theorem cell_10_38_4 : CertificateAt 10 38 4 := by decide +kernel
theorem cell_10_38_5 : CertificateAt 10 38 5 := by decide +kernel
theorem row_10_38 : ThresholdAt 10 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 38 0 cell_10_38_0
    | exact certificate_sound 10 38 1 cell_10_38_1
    | exact certificate_sound 10 38 2 cell_10_38_2
    | exact certificate_sound 10 38 3 cell_10_38_3
    | exact certificate_sound 10 38 4 cell_10_38_4
    | exact certificate_sound 10 38 5 cell_10_38_5
theorem cell_10_39_0 : CertificateAt 10 39 0 := by decide +kernel
theorem cell_10_39_1 : CertificateAt 10 39 1 := by decide +kernel
theorem cell_10_39_2 : CertificateAt 10 39 2 := by decide +kernel
theorem cell_10_39_3 : CertificateAt 10 39 3 := by decide +kernel
theorem cell_10_39_4 : CertificateAt 10 39 4 := by decide +kernel
theorem cell_10_39_5 : CertificateAt 10 39 5 := by decide +kernel
theorem row_10_39 : ThresholdAt 10 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 39 0 cell_10_39_0
    | exact certificate_sound 10 39 1 cell_10_39_1
    | exact certificate_sound 10 39 2 cell_10_39_2
    | exact certificate_sound 10 39 3 cell_10_39_3
    | exact certificate_sound 10 39 4 cell_10_39_4
    | exact certificate_sound 10 39 5 cell_10_39_5
theorem cell_10_40_0 : CertificateAt 10 40 0 := by decide +kernel
theorem cell_10_40_1 : CertificateAt 10 40 1 := by decide +kernel
theorem cell_10_40_2 : CertificateAt 10 40 2 := by decide +kernel
theorem cell_10_40_3 : CertificateAt 10 40 3 := by decide +kernel
theorem cell_10_40_4 : CertificateAt 10 40 4 := by decide +kernel
theorem cell_10_40_5 : CertificateAt 10 40 5 := by decide +kernel
theorem row_10_40 : ThresholdAt 10 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 40 0 cell_10_40_0
    | exact certificate_sound 10 40 1 cell_10_40_1
    | exact certificate_sound 10 40 2 cell_10_40_2
    | exact certificate_sound 10 40 3 cell_10_40_3
    | exact certificate_sound 10 40 4 cell_10_40_4
    | exact certificate_sound 10 40 5 cell_10_40_5
theorem cell_10_41_0 : CertificateAt 10 41 0 := by decide +kernel
theorem cell_10_41_1 : CertificateAt 10 41 1 := by decide +kernel
theorem cell_10_41_2 : CertificateAt 10 41 2 := by decide +kernel
theorem cell_10_41_3 : CertificateAt 10 41 3 := by decide +kernel
theorem cell_10_41_4 : CertificateAt 10 41 4 := by decide +kernel
theorem cell_10_41_5 : CertificateAt 10 41 5 := by decide +kernel
theorem row_10_41 : ThresholdAt 10 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 41 0 cell_10_41_0
    | exact certificate_sound 10 41 1 cell_10_41_1
    | exact certificate_sound 10 41 2 cell_10_41_2
    | exact certificate_sound 10 41 3 cell_10_41_3
    | exact certificate_sound 10 41 4 cell_10_41_4
    | exact certificate_sound 10 41 5 cell_10_41_5
theorem cell_10_42_0 : CertificateAt 10 42 0 := by decide +kernel
theorem cell_10_42_1 : CertificateAt 10 42 1 := by decide +kernel
theorem cell_10_42_2 : CertificateAt 10 42 2 := by decide +kernel
theorem cell_10_42_3 : CertificateAt 10 42 3 := by decide +kernel
theorem cell_10_42_4 : CertificateAt 10 42 4 := by decide +kernel
theorem cell_10_42_5 : CertificateAt 10 42 5 := by decide +kernel
theorem row_10_42 : ThresholdAt 10 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 42 0 cell_10_42_0
    | exact certificate_sound 10 42 1 cell_10_42_1
    | exact certificate_sound 10 42 2 cell_10_42_2
    | exact certificate_sound 10 42 3 cell_10_42_3
    | exact certificate_sound 10 42 4 cell_10_42_4
    | exact certificate_sound 10 42 5 cell_10_42_5
theorem cell_10_43_0 : CertificateAt 10 43 0 := by decide +kernel
theorem cell_10_43_1 : CertificateAt 10 43 1 := by decide +kernel
theorem cell_10_43_2 : CertificateAt 10 43 2 := by decide +kernel
theorem cell_10_43_3 : CertificateAt 10 43 3 := by decide +kernel
theorem cell_10_43_4 : CertificateAt 10 43 4 := by decide +kernel
theorem cell_10_43_5 : CertificateAt 10 43 5 := by decide +kernel
theorem row_10_43 : ThresholdAt 10 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 43 0 cell_10_43_0
    | exact certificate_sound 10 43 1 cell_10_43_1
    | exact certificate_sound 10 43 2 cell_10_43_2
    | exact certificate_sound 10 43 3 cell_10_43_3
    | exact certificate_sound 10 43 4 cell_10_43_4
    | exact certificate_sound 10 43 5 cell_10_43_5
theorem cell_10_44_0 : CertificateAt 10 44 0 := by decide +kernel
theorem cell_10_44_1 : CertificateAt 10 44 1 := by decide +kernel
theorem cell_10_44_2 : CertificateAt 10 44 2 := by decide +kernel
theorem cell_10_44_3 : CertificateAt 10 44 3 := by decide +kernel
theorem cell_10_44_4 : CertificateAt 10 44 4 := by decide +kernel
theorem cell_10_44_5 : CertificateAt 10 44 5 := by decide +kernel
theorem row_10_44 : ThresholdAt 10 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 44 0 cell_10_44_0
    | exact certificate_sound 10 44 1 cell_10_44_1
    | exact certificate_sound 10 44 2 cell_10_44_2
    | exact certificate_sound 10 44 3 cell_10_44_3
    | exact certificate_sound 10 44 4 cell_10_44_4
    | exact certificate_sound 10 44 5 cell_10_44_5
theorem cell_10_45_0 : CertificateAt 10 45 0 := by decide +kernel
theorem cell_10_45_1 : CertificateAt 10 45 1 := by decide +kernel
theorem cell_10_45_2 : CertificateAt 10 45 2 := by decide +kernel
theorem cell_10_45_3 : CertificateAt 10 45 3 := by decide +kernel
theorem cell_10_45_4 : CertificateAt 10 45 4 := by decide +kernel
theorem cell_10_45_5 : CertificateAt 10 45 5 := by decide +kernel
theorem row_10_45 : ThresholdAt 10 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 45 0 cell_10_45_0
    | exact certificate_sound 10 45 1 cell_10_45_1
    | exact certificate_sound 10 45 2 cell_10_45_2
    | exact certificate_sound 10 45 3 cell_10_45_3
    | exact certificate_sound 10 45 4 cell_10_45_4
    | exact certificate_sound 10 45 5 cell_10_45_5
theorem cell_10_46_0 : CertificateAt 10 46 0 := by decide +kernel
theorem cell_10_46_1 : CertificateAt 10 46 1 := by decide +kernel
theorem cell_10_46_2 : CertificateAt 10 46 2 := by decide +kernel
theorem cell_10_46_3 : CertificateAt 10 46 3 := by decide +kernel
theorem cell_10_46_4 : CertificateAt 10 46 4 := by decide +kernel
theorem cell_10_46_5 : CertificateAt 10 46 5 := by decide +kernel
theorem row_10_46 : ThresholdAt 10 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 46 0 cell_10_46_0
    | exact certificate_sound 10 46 1 cell_10_46_1
    | exact certificate_sound 10 46 2 cell_10_46_2
    | exact certificate_sound 10 46 3 cell_10_46_3
    | exact certificate_sound 10 46 4 cell_10_46_4
    | exact certificate_sound 10 46 5 cell_10_46_5
theorem cell_10_47_0 : CertificateAt 10 47 0 := by decide +kernel
theorem cell_10_47_1 : CertificateAt 10 47 1 := by decide +kernel
theorem cell_10_47_2 : CertificateAt 10 47 2 := by decide +kernel
theorem cell_10_47_3 : CertificateAt 10 47 3 := by decide +kernel
theorem cell_10_47_4 : CertificateAt 10 47 4 := by decide +kernel
theorem cell_10_47_5 : CertificateAt 10 47 5 := by decide +kernel
theorem row_10_47 : ThresholdAt 10 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 47 0 cell_10_47_0
    | exact certificate_sound 10 47 1 cell_10_47_1
    | exact certificate_sound 10 47 2 cell_10_47_2
    | exact certificate_sound 10 47 3 cell_10_47_3
    | exact certificate_sound 10 47 4 cell_10_47_4
    | exact certificate_sound 10 47 5 cell_10_47_5
theorem cell_10_48_0 : CertificateAt 10 48 0 := by decide +kernel
theorem cell_10_48_1 : CertificateAt 10 48 1 := by decide +kernel
theorem cell_10_48_2 : CertificateAt 10 48 2 := by decide +kernel
theorem cell_10_48_3 : CertificateAt 10 48 3 := by decide +kernel
theorem cell_10_48_4 : CertificateAt 10 48 4 := by decide +kernel
theorem cell_10_48_5 : CertificateAt 10 48 5 := by decide +kernel
theorem row_10_48 : ThresholdAt 10 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 48 0 cell_10_48_0
    | exact certificate_sound 10 48 1 cell_10_48_1
    | exact certificate_sound 10 48 2 cell_10_48_2
    | exact certificate_sound 10 48 3 cell_10_48_3
    | exact certificate_sound 10 48 4 cell_10_48_4
    | exact certificate_sound 10 48 5 cell_10_48_5
theorem cell_10_49_0 : CertificateAt 10 49 0 := by decide +kernel
theorem cell_10_49_1 : CertificateAt 10 49 1 := by decide +kernel
theorem cell_10_49_2 : CertificateAt 10 49 2 := by decide +kernel
theorem cell_10_49_3 : CertificateAt 10 49 3 := by decide +kernel
theorem cell_10_49_4 : CertificateAt 10 49 4 := by decide +kernel
theorem cell_10_49_5 : CertificateAt 10 49 5 := by decide +kernel
theorem row_10_49 : ThresholdAt 10 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 49 0 cell_10_49_0
    | exact certificate_sound 10 49 1 cell_10_49_1
    | exact certificate_sound 10 49 2 cell_10_49_2
    | exact certificate_sound 10 49 3 cell_10_49_3
    | exact certificate_sound 10 49 4 cell_10_49_4
    | exact certificate_sound 10 49 5 cell_10_49_5
theorem cell_10_50_0 : CertificateAt 10 50 0 := by decide +kernel
theorem cell_10_50_1 : CertificateAt 10 50 1 := by decide +kernel
theorem cell_10_50_2 : CertificateAt 10 50 2 := by decide +kernel
theorem cell_10_50_3 : CertificateAt 10 50 3 := by decide +kernel
theorem cell_10_50_4 : CertificateAt 10 50 4 := by decide +kernel
theorem cell_10_50_5 : CertificateAt 10 50 5 := by decide +kernel
theorem row_10_50 : ThresholdAt 10 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 50 0 cell_10_50_0
    | exact certificate_sound 10 50 1 cell_10_50_1
    | exact certificate_sound 10 50 2 cell_10_50_2
    | exact certificate_sound 10 50 3 cell_10_50_3
    | exact certificate_sound 10 50 4 cell_10_50_4
    | exact certificate_sound 10 50 5 cell_10_50_5
theorem cell_10_51_0 : CertificateAt 10 51 0 := by decide +kernel
theorem cell_10_51_1 : CertificateAt 10 51 1 := by decide +kernel
theorem cell_10_51_2 : CertificateAt 10 51 2 := by decide +kernel
theorem cell_10_51_3 : CertificateAt 10 51 3 := by decide +kernel
theorem cell_10_51_4 : CertificateAt 10 51 4 := by decide +kernel
theorem cell_10_51_5 : CertificateAt 10 51 5 := by decide +kernel
theorem row_10_51 : ThresholdAt 10 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 51 0 cell_10_51_0
    | exact certificate_sound 10 51 1 cell_10_51_1
    | exact certificate_sound 10 51 2 cell_10_51_2
    | exact certificate_sound 10 51 3 cell_10_51_3
    | exact certificate_sound 10 51 4 cell_10_51_4
    | exact certificate_sound 10 51 5 cell_10_51_5
theorem cell_10_52_0 : CertificateAt 10 52 0 := by decide +kernel
theorem cell_10_52_1 : CertificateAt 10 52 1 := by decide +kernel
theorem cell_10_52_2 : CertificateAt 10 52 2 := by decide +kernel
theorem cell_10_52_3 : CertificateAt 10 52 3 := by decide +kernel
theorem cell_10_52_4 : CertificateAt 10 52 4 := by decide +kernel
theorem cell_10_52_5 : CertificateAt 10 52 5 := by decide +kernel
theorem row_10_52 : ThresholdAt 10 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 52 0 cell_10_52_0
    | exact certificate_sound 10 52 1 cell_10_52_1
    | exact certificate_sound 10 52 2 cell_10_52_2
    | exact certificate_sound 10 52 3 cell_10_52_3
    | exact certificate_sound 10 52 4 cell_10_52_4
    | exact certificate_sound 10 52 5 cell_10_52_5
theorem cell_10_53_0 : CertificateAt 10 53 0 := by decide +kernel
theorem cell_10_53_1 : CertificateAt 10 53 1 := by decide +kernel
theorem cell_10_53_2 : CertificateAt 10 53 2 := by decide +kernel
theorem cell_10_53_3 : CertificateAt 10 53 3 := by decide +kernel
theorem cell_10_53_4 : CertificateAt 10 53 4 := by decide +kernel
theorem cell_10_53_5 : CertificateAt 10 53 5 := by decide +kernel
theorem row_10_53 : ThresholdAt 10 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 53 0 cell_10_53_0
    | exact certificate_sound 10 53 1 cell_10_53_1
    | exact certificate_sound 10 53 2 cell_10_53_2
    | exact certificate_sound 10 53 3 cell_10_53_3
    | exact certificate_sound 10 53 4 cell_10_53_4
    | exact certificate_sound 10 53 5 cell_10_53_5
theorem cell_10_54_0 : CertificateAt 10 54 0 := by decide +kernel
theorem cell_10_54_1 : CertificateAt 10 54 1 := by decide +kernel
theorem cell_10_54_2 : CertificateAt 10 54 2 := by decide +kernel
theorem cell_10_54_3 : CertificateAt 10 54 3 := by decide +kernel
theorem cell_10_54_4 : CertificateAt 10 54 4 := by decide +kernel
theorem cell_10_54_5 : CertificateAt 10 54 5 := by decide +kernel
theorem row_10_54 : ThresholdAt 10 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 54 0 cell_10_54_0
    | exact certificate_sound 10 54 1 cell_10_54_1
    | exact certificate_sound 10 54 2 cell_10_54_2
    | exact certificate_sound 10 54 3 cell_10_54_3
    | exact certificate_sound 10 54 4 cell_10_54_4
    | exact certificate_sound 10 54 5 cell_10_54_5
theorem cell_10_55_0 : CertificateAt 10 55 0 := by decide +kernel
theorem cell_10_55_1 : CertificateAt 10 55 1 := by decide +kernel
theorem cell_10_55_2 : CertificateAt 10 55 2 := by decide +kernel
theorem cell_10_55_3 : CertificateAt 10 55 3 := by decide +kernel
theorem cell_10_55_4 : CertificateAt 10 55 4 := by decide +kernel
theorem cell_10_55_5 : CertificateAt 10 55 5 := by decide +kernel
theorem row_10_55 : ThresholdAt 10 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 55 0 cell_10_55_0
    | exact certificate_sound 10 55 1 cell_10_55_1
    | exact certificate_sound 10 55 2 cell_10_55_2
    | exact certificate_sound 10 55 3 cell_10_55_3
    | exact certificate_sound 10 55 4 cell_10_55_4
    | exact certificate_sound 10 55 5 cell_10_55_5
theorem cell_10_56_0 : CertificateAt 10 56 0 := by decide +kernel
theorem cell_10_56_1 : CertificateAt 10 56 1 := by decide +kernel
theorem cell_10_56_2 : CertificateAt 10 56 2 := by decide +kernel
theorem cell_10_56_3 : CertificateAt 10 56 3 := by decide +kernel
theorem cell_10_56_4 : CertificateAt 10 56 4 := by decide +kernel
theorem cell_10_56_5 : CertificateAt 10 56 5 := by decide +kernel
theorem row_10_56 : ThresholdAt 10 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 56 0 cell_10_56_0
    | exact certificate_sound 10 56 1 cell_10_56_1
    | exact certificate_sound 10 56 2 cell_10_56_2
    | exact certificate_sound 10 56 3 cell_10_56_3
    | exact certificate_sound 10 56 4 cell_10_56_4
    | exact certificate_sound 10 56 5 cell_10_56_5
theorem cell_10_57_0 : CertificateAt 10 57 0 := by decide +kernel
theorem cell_10_57_1 : CertificateAt 10 57 1 := by decide +kernel
theorem cell_10_57_2 : CertificateAt 10 57 2 := by decide +kernel
theorem cell_10_57_3 : CertificateAt 10 57 3 := by decide +kernel
theorem cell_10_57_4 : CertificateAt 10 57 4 := by decide +kernel
theorem cell_10_57_5 : CertificateAt 10 57 5 := by decide +kernel
theorem row_10_57 : ThresholdAt 10 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 57 0 cell_10_57_0
    | exact certificate_sound 10 57 1 cell_10_57_1
    | exact certificate_sound 10 57 2 cell_10_57_2
    | exact certificate_sound 10 57 3 cell_10_57_3
    | exact certificate_sound 10 57 4 cell_10_57_4
    | exact certificate_sound 10 57 5 cell_10_57_5
theorem cell_10_58_0 : CertificateAt 10 58 0 := by decide +kernel
theorem cell_10_58_1 : CertificateAt 10 58 1 := by decide +kernel
theorem cell_10_58_2 : CertificateAt 10 58 2 := by decide +kernel
theorem cell_10_58_3 : CertificateAt 10 58 3 := by decide +kernel
theorem cell_10_58_4 : CertificateAt 10 58 4 := by decide +kernel
theorem cell_10_58_5 : CertificateAt 10 58 5 := by decide +kernel
theorem row_10_58 : ThresholdAt 10 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 58 0 cell_10_58_0
    | exact certificate_sound 10 58 1 cell_10_58_1
    | exact certificate_sound 10 58 2 cell_10_58_2
    | exact certificate_sound 10 58 3 cell_10_58_3
    | exact certificate_sound 10 58 4 cell_10_58_4
    | exact certificate_sound 10 58 5 cell_10_58_5
theorem cell_10_59_0 : CertificateAt 10 59 0 := by decide +kernel
theorem cell_10_59_1 : CertificateAt 10 59 1 := by decide +kernel
theorem cell_10_59_2 : CertificateAt 10 59 2 := by decide +kernel
theorem cell_10_59_3 : CertificateAt 10 59 3 := by decide +kernel
theorem cell_10_59_4 : CertificateAt 10 59 4 := by decide +kernel
theorem cell_10_59_5 : CertificateAt 10 59 5 := by decide +kernel
theorem row_10_59 : ThresholdAt 10 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 59 0 cell_10_59_0
    | exact certificate_sound 10 59 1 cell_10_59_1
    | exact certificate_sound 10 59 2 cell_10_59_2
    | exact certificate_sound 10 59 3 cell_10_59_3
    | exact certificate_sound 10 59 4 cell_10_59_4
    | exact certificate_sound 10 59 5 cell_10_59_5
theorem cell_10_60_0 : CertificateAt 10 60 0 := by decide +kernel
theorem cell_10_60_1 : CertificateAt 10 60 1 := by decide +kernel
theorem cell_10_60_2 : CertificateAt 10 60 2 := by decide +kernel
theorem cell_10_60_3 : CertificateAt 10 60 3 := by decide +kernel
theorem cell_10_60_4 : CertificateAt 10 60 4 := by decide +kernel
theorem cell_10_60_5 : CertificateAt 10 60 5 := by decide +kernel
theorem row_10_60 : ThresholdAt 10 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 60 0 cell_10_60_0
    | exact certificate_sound 10 60 1 cell_10_60_1
    | exact certificate_sound 10 60 2 cell_10_60_2
    | exact certificate_sound 10 60 3 cell_10_60_3
    | exact certificate_sound 10 60 4 cell_10_60_4
    | exact certificate_sound 10 60 5 cell_10_60_5
theorem cell_10_61_0 : CertificateAt 10 61 0 := by decide +kernel
theorem cell_10_61_1 : CertificateAt 10 61 1 := by decide +kernel
theorem cell_10_61_2 : CertificateAt 10 61 2 := by decide +kernel
theorem cell_10_61_3 : CertificateAt 10 61 3 := by decide +kernel
theorem cell_10_61_4 : CertificateAt 10 61 4 := by decide +kernel
theorem cell_10_61_5 : CertificateAt 10 61 5 := by decide +kernel
theorem row_10_61 : ThresholdAt 10 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 61 0 cell_10_61_0
    | exact certificate_sound 10 61 1 cell_10_61_1
    | exact certificate_sound 10 61 2 cell_10_61_2
    | exact certificate_sound 10 61 3 cell_10_61_3
    | exact certificate_sound 10 61 4 cell_10_61_4
    | exact certificate_sound 10 61 5 cell_10_61_5
theorem cell_10_62_0 : CertificateAt 10 62 0 := by decide +kernel
theorem cell_10_62_1 : CertificateAt 10 62 1 := by decide +kernel
theorem cell_10_62_2 : CertificateAt 10 62 2 := by decide +kernel
theorem cell_10_62_3 : CertificateAt 10 62 3 := by decide +kernel
theorem cell_10_62_4 : CertificateAt 10 62 4 := by decide +kernel
theorem cell_10_62_5 : CertificateAt 10 62 5 := by decide +kernel
theorem row_10_62 : ThresholdAt 10 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 62 0 cell_10_62_0
    | exact certificate_sound 10 62 1 cell_10_62_1
    | exact certificate_sound 10 62 2 cell_10_62_2
    | exact certificate_sound 10 62 3 cell_10_62_3
    | exact certificate_sound 10 62 4 cell_10_62_4
    | exact certificate_sound 10 62 5 cell_10_62_5
theorem cell_10_63_0 : CertificateAt 10 63 0 := by decide +kernel
theorem cell_10_63_1 : CertificateAt 10 63 1 := by decide +kernel
theorem cell_10_63_2 : CertificateAt 10 63 2 := by decide +kernel
theorem cell_10_63_3 : CertificateAt 10 63 3 := by decide +kernel
theorem cell_10_63_4 : CertificateAt 10 63 4 := by decide +kernel
theorem cell_10_63_5 : CertificateAt 10 63 5 := by decide +kernel
theorem row_10_63 : ThresholdAt 10 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 63 0 cell_10_63_0
    | exact certificate_sound 10 63 1 cell_10_63_1
    | exact certificate_sound 10 63 2 cell_10_63_2
    | exact certificate_sound 10 63 3 cell_10_63_3
    | exact certificate_sound 10 63 4 cell_10_63_4
    | exact certificate_sound 10 63 5 cell_10_63_5
theorem cell_10_64_0 : CertificateAt 10 64 0 := by decide +kernel
theorem cell_10_64_1 : CertificateAt 10 64 1 := by decide +kernel
theorem cell_10_64_2 : CertificateAt 10 64 2 := by decide +kernel
theorem cell_10_64_3 : CertificateAt 10 64 3 := by decide +kernel
theorem cell_10_64_4 : CertificateAt 10 64 4 := by decide +kernel
theorem cell_10_64_5 : CertificateAt 10 64 5 := by decide +kernel
theorem row_10_64 : ThresholdAt 10 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 64 0 cell_10_64_0
    | exact certificate_sound 10 64 1 cell_10_64_1
    | exact certificate_sound 10 64 2 cell_10_64_2
    | exact certificate_sound 10 64 3 cell_10_64_3
    | exact certificate_sound 10 64 4 cell_10_64_4
    | exact certificate_sound 10 64 5 cell_10_64_5
theorem cell_10_65_0 : CertificateAt 10 65 0 := by decide +kernel
theorem cell_10_65_1 : CertificateAt 10 65 1 := by decide +kernel
theorem cell_10_65_2 : CertificateAt 10 65 2 := by decide +kernel
theorem cell_10_65_3 : CertificateAt 10 65 3 := by decide +kernel
theorem cell_10_65_4 : CertificateAt 10 65 4 := by decide +kernel
theorem cell_10_65_5 : CertificateAt 10 65 5 := by decide +kernel
theorem row_10_65 : ThresholdAt 10 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 65 0 cell_10_65_0
    | exact certificate_sound 10 65 1 cell_10_65_1
    | exact certificate_sound 10 65 2 cell_10_65_2
    | exact certificate_sound 10 65 3 cell_10_65_3
    | exact certificate_sound 10 65 4 cell_10_65_4
    | exact certificate_sound 10 65 5 cell_10_65_5
theorem cell_10_66_0 : CertificateAt 10 66 0 := by decide +kernel
theorem cell_10_66_1 : CertificateAt 10 66 1 := by decide +kernel
theorem cell_10_66_2 : CertificateAt 10 66 2 := by decide +kernel
theorem cell_10_66_3 : CertificateAt 10 66 3 := by decide +kernel
theorem cell_10_66_4 : CertificateAt 10 66 4 := by decide +kernel
theorem cell_10_66_5 : CertificateAt 10 66 5 := by decide +kernel
theorem row_10_66 : ThresholdAt 10 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 66 0 cell_10_66_0
    | exact certificate_sound 10 66 1 cell_10_66_1
    | exact certificate_sound 10 66 2 cell_10_66_2
    | exact certificate_sound 10 66 3 cell_10_66_3
    | exact certificate_sound 10 66 4 cell_10_66_4
    | exact certificate_sound 10 66 5 cell_10_66_5
theorem cell_10_67_0 : CertificateAt 10 67 0 := by decide +kernel
theorem cell_10_67_1 : CertificateAt 10 67 1 := by decide +kernel
theorem cell_10_67_2 : CertificateAt 10 67 2 := by decide +kernel
theorem cell_10_67_3 : CertificateAt 10 67 3 := by decide +kernel
theorem cell_10_67_4 : CertificateAt 10 67 4 := by decide +kernel
theorem cell_10_67_5 : CertificateAt 10 67 5 := by decide +kernel
theorem row_10_67 : ThresholdAt 10 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 67 0 cell_10_67_0
    | exact certificate_sound 10 67 1 cell_10_67_1
    | exact certificate_sound 10 67 2 cell_10_67_2
    | exact certificate_sound 10 67 3 cell_10_67_3
    | exact certificate_sound 10 67 4 cell_10_67_4
    | exact certificate_sound 10 67 5 cell_10_67_5
theorem cell_10_68_0 : CertificateAt 10 68 0 := by decide +kernel
theorem cell_10_68_1 : CertificateAt 10 68 1 := by decide +kernel
theorem cell_10_68_2 : CertificateAt 10 68 2 := by decide +kernel
theorem cell_10_68_3 : CertificateAt 10 68 3 := by decide +kernel
theorem cell_10_68_4 : CertificateAt 10 68 4 := by decide +kernel
theorem cell_10_68_5 : CertificateAt 10 68 5 := by decide +kernel
theorem row_10_68 : ThresholdAt 10 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 68 0 cell_10_68_0
    | exact certificate_sound 10 68 1 cell_10_68_1
    | exact certificate_sound 10 68 2 cell_10_68_2
    | exact certificate_sound 10 68 3 cell_10_68_3
    | exact certificate_sound 10 68 4 cell_10_68_4
    | exact certificate_sound 10 68 5 cell_10_68_5
theorem cell_10_69_0 : CertificateAt 10 69 0 := by decide +kernel
theorem cell_10_69_1 : CertificateAt 10 69 1 := by decide +kernel
theorem cell_10_69_2 : CertificateAt 10 69 2 := by decide +kernel
theorem cell_10_69_3 : CertificateAt 10 69 3 := by decide +kernel
theorem cell_10_69_4 : CertificateAt 10 69 4 := by decide +kernel
theorem cell_10_69_5 : CertificateAt 10 69 5 := by decide +kernel
theorem row_10_69 : ThresholdAt 10 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 69 0 cell_10_69_0
    | exact certificate_sound 10 69 1 cell_10_69_1
    | exact certificate_sound 10 69 2 cell_10_69_2
    | exact certificate_sound 10 69 3 cell_10_69_3
    | exact certificate_sound 10 69 4 cell_10_69_4
    | exact certificate_sound 10 69 5 cell_10_69_5
theorem cell_10_70_0 : CertificateAt 10 70 0 := by decide +kernel
theorem cell_10_70_1 : CertificateAt 10 70 1 := by decide +kernel
theorem cell_10_70_2 : CertificateAt 10 70 2 := by decide +kernel
theorem cell_10_70_3 : CertificateAt 10 70 3 := by decide +kernel
theorem cell_10_70_4 : CertificateAt 10 70 4 := by decide +kernel
theorem cell_10_70_5 : CertificateAt 10 70 5 := by decide +kernel
theorem row_10_70 : ThresholdAt 10 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 70 0 cell_10_70_0
    | exact certificate_sound 10 70 1 cell_10_70_1
    | exact certificate_sound 10 70 2 cell_10_70_2
    | exact certificate_sound 10 70 3 cell_10_70_3
    | exact certificate_sound 10 70 4 cell_10_70_4
    | exact certificate_sound 10 70 5 cell_10_70_5
theorem cell_10_71_0 : CertificateAt 10 71 0 := by decide +kernel
theorem cell_10_71_1 : CertificateAt 10 71 1 := by decide +kernel
theorem cell_10_71_2 : CertificateAt 10 71 2 := by decide +kernel
theorem cell_10_71_3 : CertificateAt 10 71 3 := by decide +kernel
theorem cell_10_71_4 : CertificateAt 10 71 4 := by decide +kernel
theorem cell_10_71_5 : CertificateAt 10 71 5 := by decide +kernel
theorem row_10_71 : ThresholdAt 10 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 71 0 cell_10_71_0
    | exact certificate_sound 10 71 1 cell_10_71_1
    | exact certificate_sound 10 71 2 cell_10_71_2
    | exact certificate_sound 10 71 3 cell_10_71_3
    | exact certificate_sound 10 71 4 cell_10_71_4
    | exact certificate_sound 10 71 5 cell_10_71_5
theorem cell_10_72_0 : CertificateAt 10 72 0 := by decide +kernel
theorem cell_10_72_1 : CertificateAt 10 72 1 := by decide +kernel
theorem cell_10_72_2 : CertificateAt 10 72 2 := by decide +kernel
theorem cell_10_72_3 : CertificateAt 10 72 3 := by decide +kernel
theorem cell_10_72_4 : CertificateAt 10 72 4 := by decide +kernel
theorem cell_10_72_5 : CertificateAt 10 72 5 := by decide +kernel
theorem row_10_72 : ThresholdAt 10 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 72 0 cell_10_72_0
    | exact certificate_sound 10 72 1 cell_10_72_1
    | exact certificate_sound 10 72 2 cell_10_72_2
    | exact certificate_sound 10 72 3 cell_10_72_3
    | exact certificate_sound 10 72 4 cell_10_72_4
    | exact certificate_sound 10 72 5 cell_10_72_5
theorem cell_10_73_0 : CertificateAt 10 73 0 := by decide +kernel
theorem cell_10_73_1 : CertificateAt 10 73 1 := by decide +kernel
theorem cell_10_73_2 : CertificateAt 10 73 2 := by decide +kernel
theorem cell_10_73_3 : CertificateAt 10 73 3 := by decide +kernel
theorem cell_10_73_4 : CertificateAt 10 73 4 := by decide +kernel
theorem cell_10_73_5 : CertificateAt 10 73 5 := by decide +kernel
theorem row_10_73 : ThresholdAt 10 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 73 0 cell_10_73_0
    | exact certificate_sound 10 73 1 cell_10_73_1
    | exact certificate_sound 10 73 2 cell_10_73_2
    | exact certificate_sound 10 73 3 cell_10_73_3
    | exact certificate_sound 10 73 4 cell_10_73_4
    | exact certificate_sound 10 73 5 cell_10_73_5
theorem cell_10_74_0 : CertificateAt 10 74 0 := by decide +kernel
theorem cell_10_74_1 : CertificateAt 10 74 1 := by decide +kernel
theorem cell_10_74_2 : CertificateAt 10 74 2 := by decide +kernel
theorem cell_10_74_3 : CertificateAt 10 74 3 := by decide +kernel
theorem cell_10_74_4 : CertificateAt 10 74 4 := by decide +kernel
theorem cell_10_74_5 : CertificateAt 10 74 5 := by decide +kernel
theorem row_10_74 : ThresholdAt 10 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 74 0 cell_10_74_0
    | exact certificate_sound 10 74 1 cell_10_74_1
    | exact certificate_sound 10 74 2 cell_10_74_2
    | exact certificate_sound 10 74 3 cell_10_74_3
    | exact certificate_sound 10 74 4 cell_10_74_4
    | exact certificate_sound 10 74 5 cell_10_74_5
theorem cell_10_75_0 : CertificateAt 10 75 0 := by decide +kernel
theorem cell_10_75_1 : CertificateAt 10 75 1 := by decide +kernel
theorem cell_10_75_2 : CertificateAt 10 75 2 := by decide +kernel
theorem cell_10_75_3 : CertificateAt 10 75 3 := by decide +kernel
theorem cell_10_75_4 : CertificateAt 10 75 4 := by decide +kernel
theorem cell_10_75_5 : CertificateAt 10 75 5 := by decide +kernel
theorem row_10_75 : ThresholdAt 10 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 75 0 cell_10_75_0
    | exact certificate_sound 10 75 1 cell_10_75_1
    | exact certificate_sound 10 75 2 cell_10_75_2
    | exact certificate_sound 10 75 3 cell_10_75_3
    | exact certificate_sound 10 75 4 cell_10_75_4
    | exact certificate_sound 10 75 5 cell_10_75_5
theorem cell_10_76_0 : CertificateAt 10 76 0 := by decide +kernel
theorem cell_10_76_1 : CertificateAt 10 76 1 := by decide +kernel
theorem cell_10_76_2 : CertificateAt 10 76 2 := by decide +kernel
theorem cell_10_76_3 : CertificateAt 10 76 3 := by decide +kernel
theorem cell_10_76_4 : CertificateAt 10 76 4 := by decide +kernel
theorem cell_10_76_5 : CertificateAt 10 76 5 := by decide +kernel
theorem row_10_76 : ThresholdAt 10 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 76 0 cell_10_76_0
    | exact certificate_sound 10 76 1 cell_10_76_1
    | exact certificate_sound 10 76 2 cell_10_76_2
    | exact certificate_sound 10 76 3 cell_10_76_3
    | exact certificate_sound 10 76 4 cell_10_76_4
    | exact certificate_sound 10 76 5 cell_10_76_5
theorem cell_10_77_0 : CertificateAt 10 77 0 := by decide +kernel
theorem cell_10_77_1 : CertificateAt 10 77 1 := by decide +kernel
theorem cell_10_77_2 : CertificateAt 10 77 2 := by decide +kernel
theorem cell_10_77_3 : CertificateAt 10 77 3 := by decide +kernel
theorem cell_10_77_4 : CertificateAt 10 77 4 := by decide +kernel
theorem cell_10_77_5 : CertificateAt 10 77 5 := by decide +kernel
theorem row_10_77 : ThresholdAt 10 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 77 0 cell_10_77_0
    | exact certificate_sound 10 77 1 cell_10_77_1
    | exact certificate_sound 10 77 2 cell_10_77_2
    | exact certificate_sound 10 77 3 cell_10_77_3
    | exact certificate_sound 10 77 4 cell_10_77_4
    | exact certificate_sound 10 77 5 cell_10_77_5
theorem cell_10_78_0 : CertificateAt 10 78 0 := by decide +kernel
theorem cell_10_78_1 : CertificateAt 10 78 1 := by decide +kernel
theorem cell_10_78_2 : CertificateAt 10 78 2 := by decide +kernel
theorem cell_10_78_3 : CertificateAt 10 78 3 := by decide +kernel
theorem cell_10_78_4 : CertificateAt 10 78 4 := by decide +kernel
theorem cell_10_78_5 : CertificateAt 10 78 5 := by decide +kernel
theorem row_10_78 : ThresholdAt 10 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 78 0 cell_10_78_0
    | exact certificate_sound 10 78 1 cell_10_78_1
    | exact certificate_sound 10 78 2 cell_10_78_2
    | exact certificate_sound 10 78 3 cell_10_78_3
    | exact certificate_sound 10 78 4 cell_10_78_4
    | exact certificate_sound 10 78 5 cell_10_78_5
theorem cell_10_79_0 : CertificateAt 10 79 0 := by decide +kernel
theorem cell_10_79_1 : CertificateAt 10 79 1 := by decide +kernel
theorem cell_10_79_2 : CertificateAt 10 79 2 := by decide +kernel
theorem cell_10_79_3 : CertificateAt 10 79 3 := by decide +kernel
theorem cell_10_79_4 : CertificateAt 10 79 4 := by decide +kernel
theorem cell_10_79_5 : CertificateAt 10 79 5 := by decide +kernel
theorem row_10_79 : ThresholdAt 10 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 79 0 cell_10_79_0
    | exact certificate_sound 10 79 1 cell_10_79_1
    | exact certificate_sound 10 79 2 cell_10_79_2
    | exact certificate_sound 10 79 3 cell_10_79_3
    | exact certificate_sound 10 79 4 cell_10_79_4
    | exact certificate_sound 10 79 5 cell_10_79_5
theorem cell_10_80_0 : CertificateAt 10 80 0 := by decide +kernel
theorem cell_10_80_1 : CertificateAt 10 80 1 := by decide +kernel
theorem cell_10_80_2 : CertificateAt 10 80 2 := by decide +kernel
theorem cell_10_80_3 : CertificateAt 10 80 3 := by decide +kernel
theorem cell_10_80_4 : CertificateAt 10 80 4 := by decide +kernel
theorem cell_10_80_5 : CertificateAt 10 80 5 := by decide +kernel
theorem row_10_80 : ThresholdAt 10 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 80 0 cell_10_80_0
    | exact certificate_sound 10 80 1 cell_10_80_1
    | exact certificate_sound 10 80 2 cell_10_80_2
    | exact certificate_sound 10 80 3 cell_10_80_3
    | exact certificate_sound 10 80 4 cell_10_80_4
    | exact certificate_sound 10 80 5 cell_10_80_5
theorem cell_10_81_0 : CertificateAt 10 81 0 := by decide +kernel
theorem cell_10_81_1 : CertificateAt 10 81 1 := by decide +kernel
theorem cell_10_81_2 : CertificateAt 10 81 2 := by decide +kernel
theorem cell_10_81_3 : CertificateAt 10 81 3 := by decide +kernel
theorem cell_10_81_4 : CertificateAt 10 81 4 := by decide +kernel
theorem cell_10_81_5 : CertificateAt 10 81 5 := by decide +kernel
theorem row_10_81 : ThresholdAt 10 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 81 0 cell_10_81_0
    | exact certificate_sound 10 81 1 cell_10_81_1
    | exact certificate_sound 10 81 2 cell_10_81_2
    | exact certificate_sound 10 81 3 cell_10_81_3
    | exact certificate_sound 10 81 4 cell_10_81_4
    | exact certificate_sound 10 81 5 cell_10_81_5
theorem cell_10_82_0 : CertificateAt 10 82 0 := by decide +kernel
theorem cell_10_82_1 : CertificateAt 10 82 1 := by decide +kernel
theorem cell_10_82_2 : CertificateAt 10 82 2 := by decide +kernel
theorem cell_10_82_3 : CertificateAt 10 82 3 := by decide +kernel
theorem cell_10_82_4 : CertificateAt 10 82 4 := by decide +kernel
theorem cell_10_82_5 : CertificateAt 10 82 5 := by decide +kernel
theorem row_10_82 : ThresholdAt 10 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 82 0 cell_10_82_0
    | exact certificate_sound 10 82 1 cell_10_82_1
    | exact certificate_sound 10 82 2 cell_10_82_2
    | exact certificate_sound 10 82 3 cell_10_82_3
    | exact certificate_sound 10 82 4 cell_10_82_4
    | exact certificate_sound 10 82 5 cell_10_82_5
theorem cell_10_83_0 : CertificateAt 10 83 0 := by decide +kernel
theorem cell_10_83_1 : CertificateAt 10 83 1 := by decide +kernel
theorem cell_10_83_2 : CertificateAt 10 83 2 := by decide +kernel
theorem cell_10_83_3 : CertificateAt 10 83 3 := by decide +kernel
theorem cell_10_83_4 : CertificateAt 10 83 4 := by decide +kernel
theorem cell_10_83_5 : CertificateAt 10 83 5 := by decide +kernel
theorem row_10_83 : ThresholdAt 10 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 83 0 cell_10_83_0
    | exact certificate_sound 10 83 1 cell_10_83_1
    | exact certificate_sound 10 83 2 cell_10_83_2
    | exact certificate_sound 10 83 3 cell_10_83_3
    | exact certificate_sound 10 83 4 cell_10_83_4
    | exact certificate_sound 10 83 5 cell_10_83_5
theorem cell_10_84_0 : CertificateAt 10 84 0 := by decide +kernel
theorem cell_10_84_1 : CertificateAt 10 84 1 := by decide +kernel
theorem cell_10_84_2 : CertificateAt 10 84 2 := by decide +kernel
theorem cell_10_84_3 : CertificateAt 10 84 3 := by decide +kernel
theorem cell_10_84_4 : CertificateAt 10 84 4 := by decide +kernel
theorem cell_10_84_5 : CertificateAt 10 84 5 := by decide +kernel
theorem row_10_84 : ThresholdAt 10 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 84 0 cell_10_84_0
    | exact certificate_sound 10 84 1 cell_10_84_1
    | exact certificate_sound 10 84 2 cell_10_84_2
    | exact certificate_sound 10 84 3 cell_10_84_3
    | exact certificate_sound 10 84 4 cell_10_84_4
    | exact certificate_sound 10 84 5 cell_10_84_5
theorem cell_10_85_0 : CertificateAt 10 85 0 := by decide +kernel
theorem cell_10_85_1 : CertificateAt 10 85 1 := by decide +kernel
theorem cell_10_85_2 : CertificateAt 10 85 2 := by decide +kernel
theorem cell_10_85_3 : CertificateAt 10 85 3 := by decide +kernel
theorem cell_10_85_4 : CertificateAt 10 85 4 := by decide +kernel
theorem cell_10_85_5 : CertificateAt 10 85 5 := by decide +kernel
theorem row_10_85 : ThresholdAt 10 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 85 0 cell_10_85_0
    | exact certificate_sound 10 85 1 cell_10_85_1
    | exact certificate_sound 10 85 2 cell_10_85_2
    | exact certificate_sound 10 85 3 cell_10_85_3
    | exact certificate_sound 10 85 4 cell_10_85_4
    | exact certificate_sound 10 85 5 cell_10_85_5
theorem cell_10_86_0 : CertificateAt 10 86 0 := by decide +kernel
theorem cell_10_86_1 : CertificateAt 10 86 1 := by decide +kernel
theorem cell_10_86_2 : CertificateAt 10 86 2 := by decide +kernel
theorem cell_10_86_3 : CertificateAt 10 86 3 := by decide +kernel
theorem cell_10_86_4 : CertificateAt 10 86 4 := by decide +kernel
theorem cell_10_86_5 : CertificateAt 10 86 5 := by decide +kernel
theorem row_10_86 : ThresholdAt 10 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 86 0 cell_10_86_0
    | exact certificate_sound 10 86 1 cell_10_86_1
    | exact certificate_sound 10 86 2 cell_10_86_2
    | exact certificate_sound 10 86 3 cell_10_86_3
    | exact certificate_sound 10 86 4 cell_10_86_4
    | exact certificate_sound 10 86 5 cell_10_86_5
theorem cell_10_87_0 : CertificateAt 10 87 0 := by decide +kernel
theorem cell_10_87_1 : CertificateAt 10 87 1 := by decide +kernel
theorem cell_10_87_2 : CertificateAt 10 87 2 := by decide +kernel
theorem cell_10_87_3 : CertificateAt 10 87 3 := by decide +kernel
theorem cell_10_87_4 : CertificateAt 10 87 4 := by decide +kernel
theorem cell_10_87_5 : CertificateAt 10 87 5 := by decide +kernel
theorem row_10_87 : ThresholdAt 10 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 87 0 cell_10_87_0
    | exact certificate_sound 10 87 1 cell_10_87_1
    | exact certificate_sound 10 87 2 cell_10_87_2
    | exact certificate_sound 10 87 3 cell_10_87_3
    | exact certificate_sound 10 87 4 cell_10_87_4
    | exact certificate_sound 10 87 5 cell_10_87_5
theorem cell_10_88_0 : CertificateAt 10 88 0 := by decide +kernel
theorem cell_10_88_1 : CertificateAt 10 88 1 := by decide +kernel
theorem cell_10_88_2 : CertificateAt 10 88 2 := by decide +kernel
theorem cell_10_88_3 : CertificateAt 10 88 3 := by decide +kernel
theorem cell_10_88_4 : CertificateAt 10 88 4 := by decide +kernel
theorem cell_10_88_5 : CertificateAt 10 88 5 := by decide +kernel
theorem row_10_88 : ThresholdAt 10 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 88 0 cell_10_88_0
    | exact certificate_sound 10 88 1 cell_10_88_1
    | exact certificate_sound 10 88 2 cell_10_88_2
    | exact certificate_sound 10 88 3 cell_10_88_3
    | exact certificate_sound 10 88 4 cell_10_88_4
    | exact certificate_sound 10 88 5 cell_10_88_5
theorem cell_10_89_0 : CertificateAt 10 89 0 := by decide +kernel
theorem cell_10_89_1 : CertificateAt 10 89 1 := by decide +kernel
theorem cell_10_89_2 : CertificateAt 10 89 2 := by decide +kernel
theorem cell_10_89_3 : CertificateAt 10 89 3 := by decide +kernel
theorem cell_10_89_4 : CertificateAt 10 89 4 := by decide +kernel
theorem cell_10_89_5 : CertificateAt 10 89 5 := by decide +kernel
theorem row_10_89 : ThresholdAt 10 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 89 0 cell_10_89_0
    | exact certificate_sound 10 89 1 cell_10_89_1
    | exact certificate_sound 10 89 2 cell_10_89_2
    | exact certificate_sound 10 89 3 cell_10_89_3
    | exact certificate_sound 10 89 4 cell_10_89_4
    | exact certificate_sound 10 89 5 cell_10_89_5
theorem cell_10_90_0 : CertificateAt 10 90 0 := by decide +kernel
theorem cell_10_90_1 : CertificateAt 10 90 1 := by decide +kernel
theorem cell_10_90_2 : CertificateAt 10 90 2 := by decide +kernel
theorem cell_10_90_3 : CertificateAt 10 90 3 := by decide +kernel
theorem cell_10_90_4 : CertificateAt 10 90 4 := by decide +kernel
theorem cell_10_90_5 : CertificateAt 10 90 5 := by decide +kernel
theorem row_10_90 : ThresholdAt 10 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 90 0 cell_10_90_0
    | exact certificate_sound 10 90 1 cell_10_90_1
    | exact certificate_sound 10 90 2 cell_10_90_2
    | exact certificate_sound 10 90 3 cell_10_90_3
    | exact certificate_sound 10 90 4 cell_10_90_4
    | exact certificate_sound 10 90 5 cell_10_90_5
theorem cell_10_91_0 : CertificateAt 10 91 0 := by decide +kernel
theorem cell_10_91_1 : CertificateAt 10 91 1 := by decide +kernel
theorem cell_10_91_2 : CertificateAt 10 91 2 := by decide +kernel
theorem cell_10_91_3 : CertificateAt 10 91 3 := by decide +kernel
theorem cell_10_91_4 : CertificateAt 10 91 4 := by decide +kernel
theorem cell_10_91_5 : CertificateAt 10 91 5 := by decide +kernel
theorem row_10_91 : ThresholdAt 10 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 91 0 cell_10_91_0
    | exact certificate_sound 10 91 1 cell_10_91_1
    | exact certificate_sound 10 91 2 cell_10_91_2
    | exact certificate_sound 10 91 3 cell_10_91_3
    | exact certificate_sound 10 91 4 cell_10_91_4
    | exact certificate_sound 10 91 5 cell_10_91_5
theorem cell_10_92_0 : CertificateAt 10 92 0 := by decide +kernel
theorem cell_10_92_1 : CertificateAt 10 92 1 := by decide +kernel
theorem cell_10_92_2 : CertificateAt 10 92 2 := by decide +kernel
theorem cell_10_92_3 : CertificateAt 10 92 3 := by decide +kernel
theorem cell_10_92_4 : CertificateAt 10 92 4 := by decide +kernel
theorem cell_10_92_5 : CertificateAt 10 92 5 := by decide +kernel
theorem row_10_92 : ThresholdAt 10 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 92 0 cell_10_92_0
    | exact certificate_sound 10 92 1 cell_10_92_1
    | exact certificate_sound 10 92 2 cell_10_92_2
    | exact certificate_sound 10 92 3 cell_10_92_3
    | exact certificate_sound 10 92 4 cell_10_92_4
    | exact certificate_sound 10 92 5 cell_10_92_5
theorem cell_10_93_0 : CertificateAt 10 93 0 := by decide +kernel
theorem cell_10_93_1 : CertificateAt 10 93 1 := by decide +kernel
theorem cell_10_93_2 : CertificateAt 10 93 2 := by decide +kernel
theorem cell_10_93_3 : CertificateAt 10 93 3 := by decide +kernel
theorem cell_10_93_4 : CertificateAt 10 93 4 := by decide +kernel
theorem cell_10_93_5 : CertificateAt 10 93 5 := by decide +kernel
theorem row_10_93 : ThresholdAt 10 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 93 0 cell_10_93_0
    | exact certificate_sound 10 93 1 cell_10_93_1
    | exact certificate_sound 10 93 2 cell_10_93_2
    | exact certificate_sound 10 93 3 cell_10_93_3
    | exact certificate_sound 10 93 4 cell_10_93_4
    | exact certificate_sound 10 93 5 cell_10_93_5
theorem cell_10_94_0 : CertificateAt 10 94 0 := by decide +kernel
theorem cell_10_94_1 : CertificateAt 10 94 1 := by decide +kernel
theorem cell_10_94_2 : CertificateAt 10 94 2 := by decide +kernel
theorem cell_10_94_3 : CertificateAt 10 94 3 := by decide +kernel
theorem cell_10_94_4 : CertificateAt 10 94 4 := by decide +kernel
theorem cell_10_94_5 : CertificateAt 10 94 5 := by decide +kernel
theorem row_10_94 : ThresholdAt 10 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 94 0 cell_10_94_0
    | exact certificate_sound 10 94 1 cell_10_94_1
    | exact certificate_sound 10 94 2 cell_10_94_2
    | exact certificate_sound 10 94 3 cell_10_94_3
    | exact certificate_sound 10 94 4 cell_10_94_4
    | exact certificate_sound 10 94 5 cell_10_94_5
theorem cell_10_95_0 : CertificateAt 10 95 0 := by decide +kernel
theorem cell_10_95_1 : CertificateAt 10 95 1 := by decide +kernel
theorem cell_10_95_2 : CertificateAt 10 95 2 := by decide +kernel
theorem cell_10_95_3 : CertificateAt 10 95 3 := by decide +kernel
theorem cell_10_95_4 : CertificateAt 10 95 4 := by decide +kernel
theorem cell_10_95_5 : CertificateAt 10 95 5 := by decide +kernel
theorem row_10_95 : ThresholdAt 10 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 95 0 cell_10_95_0
    | exact certificate_sound 10 95 1 cell_10_95_1
    | exact certificate_sound 10 95 2 cell_10_95_2
    | exact certificate_sound 10 95 3 cell_10_95_3
    | exact certificate_sound 10 95 4 cell_10_95_4
    | exact certificate_sound 10 95 5 cell_10_95_5
theorem cell_10_96_0 : CertificateAt 10 96 0 := by decide +kernel
theorem cell_10_96_1 : CertificateAt 10 96 1 := by decide +kernel
theorem cell_10_96_2 : CertificateAt 10 96 2 := by decide +kernel
theorem cell_10_96_3 : CertificateAt 10 96 3 := by decide +kernel
theorem cell_10_96_4 : CertificateAt 10 96 4 := by decide +kernel
theorem cell_10_96_5 : CertificateAt 10 96 5 := by decide +kernel
theorem row_10_96 : ThresholdAt 10 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 96 0 cell_10_96_0
    | exact certificate_sound 10 96 1 cell_10_96_1
    | exact certificate_sound 10 96 2 cell_10_96_2
    | exact certificate_sound 10 96 3 cell_10_96_3
    | exact certificate_sound 10 96 4 cell_10_96_4
    | exact certificate_sound 10 96 5 cell_10_96_5
theorem cell_10_97_0 : CertificateAt 10 97 0 := by decide +kernel
theorem cell_10_97_1 : CertificateAt 10 97 1 := by decide +kernel
theorem cell_10_97_2 : CertificateAt 10 97 2 := by decide +kernel
theorem cell_10_97_3 : CertificateAt 10 97 3 := by decide +kernel
theorem cell_10_97_4 : CertificateAt 10 97 4 := by decide +kernel
theorem cell_10_97_5 : CertificateAt 10 97 5 := by decide +kernel
theorem row_10_97 : ThresholdAt 10 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 97 0 cell_10_97_0
    | exact certificate_sound 10 97 1 cell_10_97_1
    | exact certificate_sound 10 97 2 cell_10_97_2
    | exact certificate_sound 10 97 3 cell_10_97_3
    | exact certificate_sound 10 97 4 cell_10_97_4
    | exact certificate_sound 10 97 5 cell_10_97_5
theorem cell_10_98_0 : CertificateAt 10 98 0 := by decide +kernel
theorem cell_10_98_1 : CertificateAt 10 98 1 := by decide +kernel
theorem cell_10_98_2 : CertificateAt 10 98 2 := by decide +kernel
theorem cell_10_98_3 : CertificateAt 10 98 3 := by decide +kernel
theorem cell_10_98_4 : CertificateAt 10 98 4 := by decide +kernel
theorem cell_10_98_5 : CertificateAt 10 98 5 := by decide +kernel
theorem row_10_98 : ThresholdAt 10 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 98 0 cell_10_98_0
    | exact certificate_sound 10 98 1 cell_10_98_1
    | exact certificate_sound 10 98 2 cell_10_98_2
    | exact certificate_sound 10 98 3 cell_10_98_3
    | exact certificate_sound 10 98 4 cell_10_98_4
    | exact certificate_sound 10 98 5 cell_10_98_5
theorem cell_10_99_0 : CertificateAt 10 99 0 := by decide +kernel
theorem cell_10_99_1 : CertificateAt 10 99 1 := by decide +kernel
theorem cell_10_99_2 : CertificateAt 10 99 2 := by decide +kernel
theorem cell_10_99_3 : CertificateAt 10 99 3 := by decide +kernel
theorem cell_10_99_4 : CertificateAt 10 99 4 := by decide +kernel
theorem cell_10_99_5 : CertificateAt 10 99 5 := by decide +kernel
theorem row_10_99 : ThresholdAt 10 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 99 0 cell_10_99_0
    | exact certificate_sound 10 99 1 cell_10_99_1
    | exact certificate_sound 10 99 2 cell_10_99_2
    | exact certificate_sound 10 99 3 cell_10_99_3
    | exact certificate_sound 10 99 4 cell_10_99_4
    | exact certificate_sound 10 99 5 cell_10_99_5
theorem cell_10_100_0 : CertificateAt 10 100 0 := by decide +kernel
theorem cell_10_100_1 : CertificateAt 10 100 1 := by decide +kernel
theorem cell_10_100_2 : CertificateAt 10 100 2 := by decide +kernel
theorem cell_10_100_3 : CertificateAt 10 100 3 := by decide +kernel
theorem cell_10_100_4 : CertificateAt 10 100 4 := by decide +kernel
theorem cell_10_100_5 : CertificateAt 10 100 5 := by decide +kernel
theorem row_10_100 : ThresholdAt 10 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 100 0 cell_10_100_0
    | exact certificate_sound 10 100 1 cell_10_100_1
    | exact certificate_sound 10 100 2 cell_10_100_2
    | exact certificate_sound 10 100 3 cell_10_100_3
    | exact certificate_sound 10 100 4 cell_10_100_4
    | exact certificate_sound 10 100 5 cell_10_100_5
theorem cell_10_101_0 : CertificateAt 10 101 0 := by decide +kernel
theorem cell_10_101_1 : CertificateAt 10 101 1 := by decide +kernel
theorem cell_10_101_2 : CertificateAt 10 101 2 := by decide +kernel
theorem cell_10_101_3 : CertificateAt 10 101 3 := by decide +kernel
theorem cell_10_101_4 : CertificateAt 10 101 4 := by decide +kernel
theorem cell_10_101_5 : CertificateAt 10 101 5 := by decide +kernel
theorem row_10_101 : ThresholdAt 10 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 101 0 cell_10_101_0
    | exact certificate_sound 10 101 1 cell_10_101_1
    | exact certificate_sound 10 101 2 cell_10_101_2
    | exact certificate_sound 10 101 3 cell_10_101_3
    | exact certificate_sound 10 101 4 cell_10_101_4
    | exact certificate_sound 10 101 5 cell_10_101_5
theorem cell_10_102_0 : CertificateAt 10 102 0 := by decide +kernel
theorem cell_10_102_1 : CertificateAt 10 102 1 := by decide +kernel
theorem cell_10_102_2 : CertificateAt 10 102 2 := by decide +kernel
theorem cell_10_102_3 : CertificateAt 10 102 3 := by decide +kernel
theorem cell_10_102_4 : CertificateAt 10 102 4 := by decide +kernel
theorem cell_10_102_5 : CertificateAt 10 102 5 := by decide +kernel
theorem row_10_102 : ThresholdAt 10 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 102 0 cell_10_102_0
    | exact certificate_sound 10 102 1 cell_10_102_1
    | exact certificate_sound 10 102 2 cell_10_102_2
    | exact certificate_sound 10 102 3 cell_10_102_3
    | exact certificate_sound 10 102 4 cell_10_102_4
    | exact certificate_sound 10 102 5 cell_10_102_5
theorem cell_10_103_0 : CertificateAt 10 103 0 := by decide +kernel
theorem cell_10_103_1 : CertificateAt 10 103 1 := by decide +kernel
theorem cell_10_103_2 : CertificateAt 10 103 2 := by decide +kernel
theorem cell_10_103_3 : CertificateAt 10 103 3 := by decide +kernel
theorem cell_10_103_4 : CertificateAt 10 103 4 := by decide +kernel
theorem cell_10_103_5 : CertificateAt 10 103 5 := by decide +kernel
theorem row_10_103 : ThresholdAt 10 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 103 0 cell_10_103_0
    | exact certificate_sound 10 103 1 cell_10_103_1
    | exact certificate_sound 10 103 2 cell_10_103_2
    | exact certificate_sound 10 103 3 cell_10_103_3
    | exact certificate_sound 10 103 4 cell_10_103_4
    | exact certificate_sound 10 103 5 cell_10_103_5
theorem cell_10_104_0 : CertificateAt 10 104 0 := by decide +kernel
theorem cell_10_104_1 : CertificateAt 10 104 1 := by decide +kernel
theorem cell_10_104_2 : CertificateAt 10 104 2 := by decide +kernel
theorem cell_10_104_3 : CertificateAt 10 104 3 := by decide +kernel
theorem cell_10_104_4 : CertificateAt 10 104 4 := by decide +kernel
theorem cell_10_104_5 : CertificateAt 10 104 5 := by decide +kernel
theorem row_10_104 : ThresholdAt 10 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 104 0 cell_10_104_0
    | exact certificate_sound 10 104 1 cell_10_104_1
    | exact certificate_sound 10 104 2 cell_10_104_2
    | exact certificate_sound 10 104 3 cell_10_104_3
    | exact certificate_sound 10 104 4 cell_10_104_4
    | exact certificate_sound 10 104 5 cell_10_104_5
theorem cell_10_105_0 : CertificateAt 10 105 0 := by decide +kernel
theorem cell_10_105_1 : CertificateAt 10 105 1 := by decide +kernel
theorem cell_10_105_2 : CertificateAt 10 105 2 := by decide +kernel
theorem cell_10_105_3 : CertificateAt 10 105 3 := by decide +kernel
theorem cell_10_105_4 : CertificateAt 10 105 4 := by decide +kernel
theorem cell_10_105_5 : CertificateAt 10 105 5 := by decide +kernel
theorem row_10_105 : ThresholdAt 10 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 105 0 cell_10_105_0
    | exact certificate_sound 10 105 1 cell_10_105_1
    | exact certificate_sound 10 105 2 cell_10_105_2
    | exact certificate_sound 10 105 3 cell_10_105_3
    | exact certificate_sound 10 105 4 cell_10_105_4
    | exact certificate_sound 10 105 5 cell_10_105_5
theorem cell_10_106_0 : CertificateAt 10 106 0 := by decide +kernel
theorem cell_10_106_1 : CertificateAt 10 106 1 := by decide +kernel
theorem cell_10_106_2 : CertificateAt 10 106 2 := by decide +kernel
theorem cell_10_106_3 : CertificateAt 10 106 3 := by decide +kernel
theorem cell_10_106_4 : CertificateAt 10 106 4 := by decide +kernel
theorem cell_10_106_5 : CertificateAt 10 106 5 := by decide +kernel
theorem row_10_106 : ThresholdAt 10 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 106 0 cell_10_106_0
    | exact certificate_sound 10 106 1 cell_10_106_1
    | exact certificate_sound 10 106 2 cell_10_106_2
    | exact certificate_sound 10 106 3 cell_10_106_3
    | exact certificate_sound 10 106 4 cell_10_106_4
    | exact certificate_sound 10 106 5 cell_10_106_5
theorem cell_10_107_0 : CertificateAt 10 107 0 := by decide +kernel
theorem cell_10_107_1 : CertificateAt 10 107 1 := by decide +kernel
theorem cell_10_107_2 : CertificateAt 10 107 2 := by decide +kernel
theorem cell_10_107_3 : CertificateAt 10 107 3 := by decide +kernel
theorem cell_10_107_4 : CertificateAt 10 107 4 := by decide +kernel
theorem cell_10_107_5 : CertificateAt 10 107 5 := by decide +kernel
theorem row_10_107 : ThresholdAt 10 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 107 0 cell_10_107_0
    | exact certificate_sound 10 107 1 cell_10_107_1
    | exact certificate_sound 10 107 2 cell_10_107_2
    | exact certificate_sound 10 107 3 cell_10_107_3
    | exact certificate_sound 10 107 4 cell_10_107_4
    | exact certificate_sound 10 107 5 cell_10_107_5
theorem cell_10_108_0 : CertificateAt 10 108 0 := by decide +kernel
theorem cell_10_108_1 : CertificateAt 10 108 1 := by decide +kernel
theorem cell_10_108_2 : CertificateAt 10 108 2 := by decide +kernel
theorem cell_10_108_3 : CertificateAt 10 108 3 := by decide +kernel
theorem cell_10_108_4 : CertificateAt 10 108 4 := by decide +kernel
theorem cell_10_108_5 : CertificateAt 10 108 5 := by decide +kernel
theorem row_10_108 : ThresholdAt 10 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 108 0 cell_10_108_0
    | exact certificate_sound 10 108 1 cell_10_108_1
    | exact certificate_sound 10 108 2 cell_10_108_2
    | exact certificate_sound 10 108 3 cell_10_108_3
    | exact certificate_sound 10 108 4 cell_10_108_4
    | exact certificate_sound 10 108 5 cell_10_108_5
theorem cell_10_109_0 : CertificateAt 10 109 0 := by decide +kernel
theorem cell_10_109_1 : CertificateAt 10 109 1 := by decide +kernel
theorem cell_10_109_2 : CertificateAt 10 109 2 := by decide +kernel
theorem cell_10_109_3 : CertificateAt 10 109 3 := by decide +kernel
theorem cell_10_109_4 : CertificateAt 10 109 4 := by decide +kernel
theorem cell_10_109_5 : CertificateAt 10 109 5 := by decide +kernel
theorem row_10_109 : ThresholdAt 10 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 109 0 cell_10_109_0
    | exact certificate_sound 10 109 1 cell_10_109_1
    | exact certificate_sound 10 109 2 cell_10_109_2
    | exact certificate_sound 10 109 3 cell_10_109_3
    | exact certificate_sound 10 109 4 cell_10_109_4
    | exact certificate_sound 10 109 5 cell_10_109_5
theorem cell_10_110_0 : CertificateAt 10 110 0 := by decide +kernel
theorem cell_10_110_1 : CertificateAt 10 110 1 := by decide +kernel
theorem cell_10_110_2 : CertificateAt 10 110 2 := by decide +kernel
theorem cell_10_110_3 : CertificateAt 10 110 3 := by decide +kernel
theorem cell_10_110_4 : CertificateAt 10 110 4 := by decide +kernel
theorem cell_10_110_5 : CertificateAt 10 110 5 := by decide +kernel
theorem row_10_110 : ThresholdAt 10 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 110 0 cell_10_110_0
    | exact certificate_sound 10 110 1 cell_10_110_1
    | exact certificate_sound 10 110 2 cell_10_110_2
    | exact certificate_sound 10 110 3 cell_10_110_3
    | exact certificate_sound 10 110 4 cell_10_110_4
    | exact certificate_sound 10 110 5 cell_10_110_5
theorem cell_10_111_0 : CertificateAt 10 111 0 := by decide +kernel
theorem cell_10_111_1 : CertificateAt 10 111 1 := by decide +kernel
theorem cell_10_111_2 : CertificateAt 10 111 2 := by decide +kernel
theorem cell_10_111_3 : CertificateAt 10 111 3 := by decide +kernel
theorem cell_10_111_4 : CertificateAt 10 111 4 := by decide +kernel
theorem cell_10_111_5 : CertificateAt 10 111 5 := by decide +kernel
theorem row_10_111 : ThresholdAt 10 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 111 0 cell_10_111_0
    | exact certificate_sound 10 111 1 cell_10_111_1
    | exact certificate_sound 10 111 2 cell_10_111_2
    | exact certificate_sound 10 111 3 cell_10_111_3
    | exact certificate_sound 10 111 4 cell_10_111_4
    | exact certificate_sound 10 111 5 cell_10_111_5
theorem cell_10_112_0 : CertificateAt 10 112 0 := by decide +kernel
theorem cell_10_112_1 : CertificateAt 10 112 1 := by decide +kernel
theorem cell_10_112_2 : CertificateAt 10 112 2 := by decide +kernel
theorem cell_10_112_3 : CertificateAt 10 112 3 := by decide +kernel
theorem cell_10_112_4 : CertificateAt 10 112 4 := by decide +kernel
theorem cell_10_112_5 : CertificateAt 10 112 5 := by decide +kernel
theorem row_10_112 : ThresholdAt 10 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 112 0 cell_10_112_0
    | exact certificate_sound 10 112 1 cell_10_112_1
    | exact certificate_sound 10 112 2 cell_10_112_2
    | exact certificate_sound 10 112 3 cell_10_112_3
    | exact certificate_sound 10 112 4 cell_10_112_4
    | exact certificate_sound 10 112 5 cell_10_112_5
theorem cell_10_113_0 : CertificateAt 10 113 0 := by decide +kernel
theorem cell_10_113_1 : CertificateAt 10 113 1 := by decide +kernel
theorem cell_10_113_2 : CertificateAt 10 113 2 := by decide +kernel
theorem cell_10_113_3 : CertificateAt 10 113 3 := by decide +kernel
theorem cell_10_113_4 : CertificateAt 10 113 4 := by decide +kernel
theorem cell_10_113_5 : CertificateAt 10 113 5 := by decide +kernel
theorem row_10_113 : ThresholdAt 10 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 113 0 cell_10_113_0
    | exact certificate_sound 10 113 1 cell_10_113_1
    | exact certificate_sound 10 113 2 cell_10_113_2
    | exact certificate_sound 10 113 3 cell_10_113_3
    | exact certificate_sound 10 113 4 cell_10_113_4
    | exact certificate_sound 10 113 5 cell_10_113_5
theorem cell_10_114_0 : CertificateAt 10 114 0 := by decide +kernel
theorem cell_10_114_1 : CertificateAt 10 114 1 := by decide +kernel
theorem cell_10_114_2 : CertificateAt 10 114 2 := by decide +kernel
theorem cell_10_114_3 : CertificateAt 10 114 3 := by decide +kernel
theorem cell_10_114_4 : CertificateAt 10 114 4 := by decide +kernel
theorem cell_10_114_5 : CertificateAt 10 114 5 := by decide +kernel
theorem row_10_114 : ThresholdAt 10 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 114 0 cell_10_114_0
    | exact certificate_sound 10 114 1 cell_10_114_1
    | exact certificate_sound 10 114 2 cell_10_114_2
    | exact certificate_sound 10 114 3 cell_10_114_3
    | exact certificate_sound 10 114 4 cell_10_114_4
    | exact certificate_sound 10 114 5 cell_10_114_5
theorem cell_10_115_0 : CertificateAt 10 115 0 := by decide +kernel
theorem cell_10_115_1 : CertificateAt 10 115 1 := by decide +kernel
theorem cell_10_115_2 : CertificateAt 10 115 2 := by decide +kernel
theorem cell_10_115_3 : CertificateAt 10 115 3 := by decide +kernel
theorem cell_10_115_4 : CertificateAt 10 115 4 := by decide +kernel
theorem cell_10_115_5 : CertificateAt 10 115 5 := by decide +kernel
theorem row_10_115 : ThresholdAt 10 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 115 0 cell_10_115_0
    | exact certificate_sound 10 115 1 cell_10_115_1
    | exact certificate_sound 10 115 2 cell_10_115_2
    | exact certificate_sound 10 115 3 cell_10_115_3
    | exact certificate_sound 10 115 4 cell_10_115_4
    | exact certificate_sound 10 115 5 cell_10_115_5
theorem cell_10_116_0 : CertificateAt 10 116 0 := by decide +kernel
theorem cell_10_116_1 : CertificateAt 10 116 1 := by decide +kernel
theorem cell_10_116_2 : CertificateAt 10 116 2 := by decide +kernel
theorem cell_10_116_3 : CertificateAt 10 116 3 := by decide +kernel
theorem cell_10_116_4 : CertificateAt 10 116 4 := by decide +kernel
theorem cell_10_116_5 : CertificateAt 10 116 5 := by decide +kernel
theorem row_10_116 : ThresholdAt 10 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 116 0 cell_10_116_0
    | exact certificate_sound 10 116 1 cell_10_116_1
    | exact certificate_sound 10 116 2 cell_10_116_2
    | exact certificate_sound 10 116 3 cell_10_116_3
    | exact certificate_sound 10 116 4 cell_10_116_4
    | exact certificate_sound 10 116 5 cell_10_116_5
theorem cell_10_117_0 : CertificateAt 10 117 0 := by decide +kernel
theorem cell_10_117_1 : CertificateAt 10 117 1 := by decide +kernel
theorem cell_10_117_2 : CertificateAt 10 117 2 := by decide +kernel
theorem cell_10_117_3 : CertificateAt 10 117 3 := by decide +kernel
theorem cell_10_117_4 : CertificateAt 10 117 4 := by decide +kernel
theorem cell_10_117_5 : CertificateAt 10 117 5 := by decide +kernel
theorem row_10_117 : ThresholdAt 10 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 117 0 cell_10_117_0
    | exact certificate_sound 10 117 1 cell_10_117_1
    | exact certificate_sound 10 117 2 cell_10_117_2
    | exact certificate_sound 10 117 3 cell_10_117_3
    | exact certificate_sound 10 117 4 cell_10_117_4
    | exact certificate_sound 10 117 5 cell_10_117_5
theorem cell_10_118_0 : CertificateAt 10 118 0 := by decide +kernel
theorem cell_10_118_1 : CertificateAt 10 118 1 := by decide +kernel
theorem cell_10_118_2 : CertificateAt 10 118 2 := by decide +kernel
theorem cell_10_118_3 : CertificateAt 10 118 3 := by decide +kernel
theorem cell_10_118_4 : CertificateAt 10 118 4 := by decide +kernel
theorem cell_10_118_5 : CertificateAt 10 118 5 := by decide +kernel
theorem row_10_118 : ThresholdAt 10 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 118 0 cell_10_118_0
    | exact certificate_sound 10 118 1 cell_10_118_1
    | exact certificate_sound 10 118 2 cell_10_118_2
    | exact certificate_sound 10 118 3 cell_10_118_3
    | exact certificate_sound 10 118 4 cell_10_118_4
    | exact certificate_sound 10 118 5 cell_10_118_5
theorem cell_10_119_0 : CertificateAt 10 119 0 := by decide +kernel
theorem cell_10_119_1 : CertificateAt 10 119 1 := by decide +kernel
theorem cell_10_119_2 : CertificateAt 10 119 2 := by decide +kernel
theorem cell_10_119_3 : CertificateAt 10 119 3 := by decide +kernel
theorem cell_10_119_4 : CertificateAt 10 119 4 := by decide +kernel
theorem cell_10_119_5 : CertificateAt 10 119 5 := by decide +kernel
theorem row_10_119 : ThresholdAt 10 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 119 0 cell_10_119_0
    | exact certificate_sound 10 119 1 cell_10_119_1
    | exact certificate_sound 10 119 2 cell_10_119_2
    | exact certificate_sound 10 119 3 cell_10_119_3
    | exact certificate_sound 10 119 4 cell_10_119_4
    | exact certificate_sound 10 119 5 cell_10_119_5
theorem cell_10_120_0 : CertificateAt 10 120 0 := by decide +kernel
theorem cell_10_120_1 : CertificateAt 10 120 1 := by decide +kernel
theorem cell_10_120_2 : CertificateAt 10 120 2 := by decide +kernel
theorem cell_10_120_3 : CertificateAt 10 120 3 := by decide +kernel
theorem cell_10_120_4 : CertificateAt 10 120 4 := by decide +kernel
theorem cell_10_120_5 : CertificateAt 10 120 5 := by decide +kernel
theorem row_10_120 : ThresholdAt 10 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 120 0 cell_10_120_0
    | exact certificate_sound 10 120 1 cell_10_120_1
    | exact certificate_sound 10 120 2 cell_10_120_2
    | exact certificate_sound 10 120 3 cell_10_120_3
    | exact certificate_sound 10 120 4 cell_10_120_4
    | exact certificate_sound 10 120 5 cell_10_120_5
theorem cell_10_121_0 : CertificateAt 10 121 0 := by decide +kernel
theorem cell_10_121_1 : CertificateAt 10 121 1 := by decide +kernel
theorem cell_10_121_2 : CertificateAt 10 121 2 := by decide +kernel
theorem cell_10_121_3 : CertificateAt 10 121 3 := by decide +kernel
theorem cell_10_121_4 : CertificateAt 10 121 4 := by decide +kernel
theorem cell_10_121_5 : CertificateAt 10 121 5 := by decide +kernel
theorem row_10_121 : ThresholdAt 10 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 121 0 cell_10_121_0
    | exact certificate_sound 10 121 1 cell_10_121_1
    | exact certificate_sound 10 121 2 cell_10_121_2
    | exact certificate_sound 10 121 3 cell_10_121_3
    | exact certificate_sound 10 121 4 cell_10_121_4
    | exact certificate_sound 10 121 5 cell_10_121_5
theorem cell_10_122_0 : CertificateAt 10 122 0 := by decide +kernel
theorem cell_10_122_1 : CertificateAt 10 122 1 := by decide +kernel
theorem cell_10_122_2 : CertificateAt 10 122 2 := by decide +kernel
theorem cell_10_122_3 : CertificateAt 10 122 3 := by decide +kernel
theorem cell_10_122_4 : CertificateAt 10 122 4 := by decide +kernel
theorem cell_10_122_5 : CertificateAt 10 122 5 := by decide +kernel
theorem row_10_122 : ThresholdAt 10 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 122 0 cell_10_122_0
    | exact certificate_sound 10 122 1 cell_10_122_1
    | exact certificate_sound 10 122 2 cell_10_122_2
    | exact certificate_sound 10 122 3 cell_10_122_3
    | exact certificate_sound 10 122 4 cell_10_122_4
    | exact certificate_sound 10 122 5 cell_10_122_5
theorem cell_10_123_0 : CertificateAt 10 123 0 := by decide +kernel
theorem cell_10_123_1 : CertificateAt 10 123 1 := by decide +kernel
theorem cell_10_123_2 : CertificateAt 10 123 2 := by decide +kernel
theorem cell_10_123_3 : CertificateAt 10 123 3 := by decide +kernel
theorem cell_10_123_4 : CertificateAt 10 123 4 := by decide +kernel
theorem cell_10_123_5 : CertificateAt 10 123 5 := by decide +kernel
theorem row_10_123 : ThresholdAt 10 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 123 0 cell_10_123_0
    | exact certificate_sound 10 123 1 cell_10_123_1
    | exact certificate_sound 10 123 2 cell_10_123_2
    | exact certificate_sound 10 123 3 cell_10_123_3
    | exact certificate_sound 10 123 4 cell_10_123_4
    | exact certificate_sound 10 123 5 cell_10_123_5
theorem cell_10_124_0 : CertificateAt 10 124 0 := by decide +kernel
theorem cell_10_124_1 : CertificateAt 10 124 1 := by decide +kernel
theorem cell_10_124_2 : CertificateAt 10 124 2 := by decide +kernel
theorem cell_10_124_3 : CertificateAt 10 124 3 := by decide +kernel
theorem cell_10_124_4 : CertificateAt 10 124 4 := by decide +kernel
theorem cell_10_124_5 : CertificateAt 10 124 5 := by decide +kernel
theorem row_10_124 : ThresholdAt 10 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 124 0 cell_10_124_0
    | exact certificate_sound 10 124 1 cell_10_124_1
    | exact certificate_sound 10 124 2 cell_10_124_2
    | exact certificate_sound 10 124 3 cell_10_124_3
    | exact certificate_sound 10 124 4 cell_10_124_4
    | exact certificate_sound 10 124 5 cell_10_124_5
theorem cell_10_125_0 : CertificateAt 10 125 0 := by decide +kernel
theorem cell_10_125_1 : CertificateAt 10 125 1 := by decide +kernel
theorem cell_10_125_2 : CertificateAt 10 125 2 := by decide +kernel
theorem cell_10_125_3 : CertificateAt 10 125 3 := by decide +kernel
theorem cell_10_125_4 : CertificateAt 10 125 4 := by decide +kernel
theorem cell_10_125_5 : CertificateAt 10 125 5 := by decide +kernel
theorem row_10_125 : ThresholdAt 10 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 125 0 cell_10_125_0
    | exact certificate_sound 10 125 1 cell_10_125_1
    | exact certificate_sound 10 125 2 cell_10_125_2
    | exact certificate_sound 10 125 3 cell_10_125_3
    | exact certificate_sound 10 125 4 cell_10_125_4
    | exact certificate_sound 10 125 5 cell_10_125_5
theorem cell_10_126_0 : CertificateAt 10 126 0 := by decide +kernel
theorem cell_10_126_1 : CertificateAt 10 126 1 := by decide +kernel
theorem cell_10_126_2 : CertificateAt 10 126 2 := by decide +kernel
theorem cell_10_126_3 : CertificateAt 10 126 3 := by decide +kernel
theorem cell_10_126_4 : CertificateAt 10 126 4 := by decide +kernel
theorem cell_10_126_5 : CertificateAt 10 126 5 := by decide +kernel
theorem row_10_126 : ThresholdAt 10 126 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 126 0 cell_10_126_0
    | exact certificate_sound 10 126 1 cell_10_126_1
    | exact certificate_sound 10 126 2 cell_10_126_2
    | exact certificate_sound 10 126 3 cell_10_126_3
    | exact certificate_sound 10 126 4 cell_10_126_4
    | exact certificate_sound 10 126 5 cell_10_126_5
theorem cell_10_127_0 : CertificateAt 10 127 0 := by decide +kernel
theorem cell_10_127_1 : CertificateAt 10 127 1 := by decide +kernel
theorem cell_10_127_2 : CertificateAt 10 127 2 := by decide +kernel
theorem cell_10_127_3 : CertificateAt 10 127 3 := by decide +kernel
theorem cell_10_127_4 : CertificateAt 10 127 4 := by decide +kernel
theorem cell_10_127_5 : CertificateAt 10 127 5 := by decide +kernel
theorem row_10_127 : ThresholdAt 10 127 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 127 0 cell_10_127_0
    | exact certificate_sound 10 127 1 cell_10_127_1
    | exact certificate_sound 10 127 2 cell_10_127_2
    | exact certificate_sound 10 127 3 cell_10_127_3
    | exact certificate_sound 10 127 4 cell_10_127_4
    | exact certificate_sound 10 127 5 cell_10_127_5
theorem cell_10_128_0 : CertificateAt 10 128 0 := by decide +kernel
theorem cell_10_128_1 : CertificateAt 10 128 1 := by decide +kernel
theorem cell_10_128_2 : CertificateAt 10 128 2 := by decide +kernel
theorem cell_10_128_3 : CertificateAt 10 128 3 := by decide +kernel
theorem cell_10_128_4 : CertificateAt 10 128 4 := by decide +kernel
theorem cell_10_128_5 : CertificateAt 10 128 5 := by decide +kernel
theorem row_10_128 : ThresholdAt 10 128 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 128 0 cell_10_128_0
    | exact certificate_sound 10 128 1 cell_10_128_1
    | exact certificate_sound 10 128 2 cell_10_128_2
    | exact certificate_sound 10 128 3 cell_10_128_3
    | exact certificate_sound 10 128 4 cell_10_128_4
    | exact certificate_sound 10 128 5 cell_10_128_5
theorem cell_10_129_0 : CertificateAt 10 129 0 := by decide +kernel
theorem cell_10_129_1 : CertificateAt 10 129 1 := by decide +kernel
theorem cell_10_129_2 : CertificateAt 10 129 2 := by decide +kernel
theorem cell_10_129_3 : CertificateAt 10 129 3 := by decide +kernel
theorem cell_10_129_4 : CertificateAt 10 129 4 := by decide +kernel
theorem cell_10_129_5 : CertificateAt 10 129 5 := by decide +kernel
theorem row_10_129 : ThresholdAt 10 129 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 10 129 0 cell_10_129_0
    | exact certificate_sound 10 129 1 cell_10_129_1
    | exact certificate_sound 10 129 2 cell_10_129_2
    | exact certificate_sound 10 129 3 cell_10_129_3
    | exact certificate_sound 10 129 4 cell_10_129_4
    | exact certificate_sound 10 129 5 cell_10_129_5
theorem checkedR10 : ∀ V ∈ List.range 130, ThresholdAt 10 V := by
  intro V hV
  have hv : V < 130 := List.mem_range.mp hV
  by_cases h0_130 : V < 65
  · by_cases h0_65 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_10_0
              · have he : V = 1 := by omega
                subst V
                exact row_10_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_10_2
              · have he : V = 3 := by omega
                subst V
                exact row_10_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_10_4
              · have he : V = 5 := by omega
                subst V
                exact row_10_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_10_6
              · have he : V = 7 := by omega
                subst V
                exact row_10_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_10_8
              · have he : V = 9 := by omega
                subst V
                exact row_10_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_10_10
              · have he : V = 11 := by omega
                subst V
                exact row_10_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_10_12
              · have he : V = 13 := by omega
                subst V
                exact row_10_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_10_14
              · have he : V = 15 := by omega
                subst V
                exact row_10_15
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_10_16
              · have he : V = 17 := by omega
                subst V
                exact row_10_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_10_18
              · have he : V = 19 := by omega
                subst V
                exact row_10_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_10_20
              · have he : V = 21 := by omega
                subst V
                exact row_10_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_10_22
              · have he : V = 23 := by omega
                subst V
                exact row_10_23
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_10_24
              · have he : V = 25 := by omega
                subst V
                exact row_10_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_10_26
              · have he : V = 27 := by omega
                subst V
                exact row_10_27
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_10_28
              · have he : V = 29 := by omega
                subst V
                exact row_10_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_10_30
              · have he : V = 31 := by omega
                subst V
                exact row_10_31
    · by_cases h32_65 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_10_32
              · have he : V = 33 := by omega
                subst V
                exact row_10_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_10_34
              · have he : V = 35 := by omega
                subst V
                exact row_10_35
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_10_36
              · have he : V = 37 := by omega
                subst V
                exact row_10_37
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_10_38
              · have he : V = 39 := by omega
                subst V
                exact row_10_39
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_10_40
              · have he : V = 41 := by omega
                subst V
                exact row_10_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_10_42
              · have he : V = 43 := by omega
                subst V
                exact row_10_43
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_10_44
              · have he : V = 45 := by omega
                subst V
                exact row_10_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_10_46
              · have he : V = 47 := by omega
                subst V
                exact row_10_47
      · by_cases h48_65 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_10_48
              · have he : V = 49 := by omega
                subst V
                exact row_10_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_10_50
              · have he : V = 51 := by omega
                subst V
                exact row_10_51
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_10_52
              · have he : V = 53 := by omega
                subst V
                exact row_10_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_10_54
              · have he : V = 55 := by omega
                subst V
                exact row_10_55
        · by_cases h56_65 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_10_56
              · have he : V = 57 := by omega
                subst V
                exact row_10_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_10_58
              · have he : V = 59 := by omega
                subst V
                exact row_10_59
          · by_cases h60_65 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_10_60
              · have he : V = 61 := by omega
                subst V
                exact row_10_61
            · by_cases h62_65 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_10_62
              · by_cases h63_65 : V < 64
                · have he : V = 63 := by omega
                  subst V
                  exact row_10_63
                · have he : V = 64 := by omega
                  subst V
                  exact row_10_64
  · by_cases h65_130 : V < 97
    · by_cases h65_97 : V < 81
      · by_cases h65_81 : V < 73
        · by_cases h65_73 : V < 69
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_10_65
              · have he : V = 66 := by omega
                subst V
                exact row_10_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_10_67
              · have he : V = 68 := by omega
                subst V
                exact row_10_68
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_10_69
              · have he : V = 70 := by omega
                subst V
                exact row_10_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_10_71
              · have he : V = 72 := by omega
                subst V
                exact row_10_72
        · by_cases h73_81 : V < 77
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_10_73
              · have he : V = 74 := by omega
                subst V
                exact row_10_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_10_75
              · have he : V = 76 := by omega
                subst V
                exact row_10_76
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_10_77
              · have he : V = 78 := by omega
                subst V
                exact row_10_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_10_79
              · have he : V = 80 := by omega
                subst V
                exact row_10_80
      · by_cases h81_97 : V < 89
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_10_81
              · have he : V = 82 := by omega
                subst V
                exact row_10_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_10_83
              · have he : V = 84 := by omega
                subst V
                exact row_10_84
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_10_85
              · have he : V = 86 := by omega
                subst V
                exact row_10_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_10_87
              · have he : V = 88 := by omega
                subst V
                exact row_10_88
        · by_cases h89_97 : V < 93
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_10_89
              · have he : V = 90 := by omega
                subst V
                exact row_10_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_10_91
              · have he : V = 92 := by omega
                subst V
                exact row_10_92
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_10_93
              · have he : V = 94 := by omega
                subst V
                exact row_10_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_10_95
              · have he : V = 96 := by omega
                subst V
                exact row_10_96
    · by_cases h97_130 : V < 113
      · by_cases h97_113 : V < 105
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_10_97
              · have he : V = 98 := by omega
                subst V
                exact row_10_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_10_99
              · have he : V = 100 := by omega
                subst V
                exact row_10_100
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_10_101
              · have he : V = 102 := by omega
                subst V
                exact row_10_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_10_103
              · have he : V = 104 := by omega
                subst V
                exact row_10_104
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_10_105
              · have he : V = 106 := by omega
                subst V
                exact row_10_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_10_107
              · have he : V = 108 := by omega
                subst V
                exact row_10_108
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_10_109
              · have he : V = 110 := by omega
                subst V
                exact row_10_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_10_111
              · have he : V = 112 := by omega
                subst V
                exact row_10_112
      · by_cases h113_130 : V < 121
        · by_cases h113_121 : V < 117
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_10_113
              · have he : V = 114 := by omega
                subst V
                exact row_10_114
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_10_115
              · have he : V = 116 := by omega
                subst V
                exact row_10_116
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_10_117
              · have he : V = 118 := by omega
                subst V
                exact row_10_118
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_10_119
              · have he : V = 120 := by omega
                subst V
                exact row_10_120
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_10_121
              · have he : V = 122 := by omega
                subst V
                exact row_10_122
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_10_123
              · have he : V = 124 := by omega
                subst V
                exact row_10_124
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_10_125
              · have he : V = 126 := by omega
                subst V
                exact row_10_126
            · by_cases h127_130 : V < 128
              · have he : V = 127 := by omega
                subst V
                exact row_10_127
              · by_cases h128_130 : V < 129
                · have he : V = 128 := by omega
                  subst V
                  exact row_10_128
                · have he : V = 129 := by omega
                  subst V
                  exact row_10_129
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
