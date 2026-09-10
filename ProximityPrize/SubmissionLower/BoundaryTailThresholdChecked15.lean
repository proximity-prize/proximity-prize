import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked14

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_15_0_0 : CertificateAt 15 0 0 := by decide +kernel
theorem cell_15_0_1 : CertificateAt 15 0 1 := by decide +kernel
theorem cell_15_0_2 : CertificateAt 15 0 2 := by decide +kernel
theorem cell_15_0_3 : CertificateAt 15 0 3 := by decide +kernel
theorem cell_15_0_4 : CertificateAt 15 0 4 := by decide +kernel
theorem cell_15_0_5 : CertificateAt 15 0 5 := by decide +kernel
theorem row_15_0 : ThresholdAt 15 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 0 0 cell_15_0_0
    | exact certificate_sound 15 0 1 cell_15_0_1
    | exact certificate_sound 15 0 2 cell_15_0_2
    | exact certificate_sound 15 0 3 cell_15_0_3
    | exact certificate_sound 15 0 4 cell_15_0_4
    | exact certificate_sound 15 0 5 cell_15_0_5
theorem cell_15_1_0 : CertificateAt 15 1 0 := by decide +kernel
theorem cell_15_1_1 : CertificateAt 15 1 1 := by decide +kernel
theorem cell_15_1_2 : CertificateAt 15 1 2 := by decide +kernel
theorem cell_15_1_3 : CertificateAt 15 1 3 := by decide +kernel
theorem cell_15_1_4 : CertificateAt 15 1 4 := by decide +kernel
theorem cell_15_1_5 : CertificateAt 15 1 5 := by decide +kernel
theorem row_15_1 : ThresholdAt 15 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 1 0 cell_15_1_0
    | exact certificate_sound 15 1 1 cell_15_1_1
    | exact certificate_sound 15 1 2 cell_15_1_2
    | exact certificate_sound 15 1 3 cell_15_1_3
    | exact certificate_sound 15 1 4 cell_15_1_4
    | exact certificate_sound 15 1 5 cell_15_1_5
theorem cell_15_2_0 : CertificateAt 15 2 0 := by decide +kernel
theorem cell_15_2_1 : CertificateAt 15 2 1 := by decide +kernel
theorem cell_15_2_2 : CertificateAt 15 2 2 := by decide +kernel
theorem cell_15_2_3 : CertificateAt 15 2 3 := by decide +kernel
theorem cell_15_2_4 : CertificateAt 15 2 4 := by decide +kernel
theorem cell_15_2_5 : CertificateAt 15 2 5 := by decide +kernel
theorem row_15_2 : ThresholdAt 15 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 2 0 cell_15_2_0
    | exact certificate_sound 15 2 1 cell_15_2_1
    | exact certificate_sound 15 2 2 cell_15_2_2
    | exact certificate_sound 15 2 3 cell_15_2_3
    | exact certificate_sound 15 2 4 cell_15_2_4
    | exact certificate_sound 15 2 5 cell_15_2_5
theorem cell_15_3_0 : CertificateAt 15 3 0 := by decide +kernel
theorem cell_15_3_1 : CertificateAt 15 3 1 := by decide +kernel
theorem cell_15_3_2 : CertificateAt 15 3 2 := by decide +kernel
theorem cell_15_3_3 : CertificateAt 15 3 3 := by decide +kernel
theorem cell_15_3_4 : CertificateAt 15 3 4 := by decide +kernel
theorem cell_15_3_5 : CertificateAt 15 3 5 := by decide +kernel
theorem row_15_3 : ThresholdAt 15 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 3 0 cell_15_3_0
    | exact certificate_sound 15 3 1 cell_15_3_1
    | exact certificate_sound 15 3 2 cell_15_3_2
    | exact certificate_sound 15 3 3 cell_15_3_3
    | exact certificate_sound 15 3 4 cell_15_3_4
    | exact certificate_sound 15 3 5 cell_15_3_5
theorem cell_15_4_0 : CertificateAt 15 4 0 := by decide +kernel
theorem cell_15_4_1 : CertificateAt 15 4 1 := by decide +kernel
theorem cell_15_4_2 : CertificateAt 15 4 2 := by decide +kernel
theorem cell_15_4_3 : CertificateAt 15 4 3 := by decide +kernel
theorem cell_15_4_4 : CertificateAt 15 4 4 := by decide +kernel
theorem cell_15_4_5 : CertificateAt 15 4 5 := by decide +kernel
theorem row_15_4 : ThresholdAt 15 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 4 0 cell_15_4_0
    | exact certificate_sound 15 4 1 cell_15_4_1
    | exact certificate_sound 15 4 2 cell_15_4_2
    | exact certificate_sound 15 4 3 cell_15_4_3
    | exact certificate_sound 15 4 4 cell_15_4_4
    | exact certificate_sound 15 4 5 cell_15_4_5
theorem cell_15_5_0 : CertificateAt 15 5 0 := by decide +kernel
theorem cell_15_5_1 : CertificateAt 15 5 1 := by decide +kernel
theorem cell_15_5_2 : CertificateAt 15 5 2 := by decide +kernel
theorem cell_15_5_3 : CertificateAt 15 5 3 := by decide +kernel
theorem cell_15_5_4 : CertificateAt 15 5 4 := by decide +kernel
theorem cell_15_5_5 : CertificateAt 15 5 5 := by decide +kernel
theorem row_15_5 : ThresholdAt 15 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 5 0 cell_15_5_0
    | exact certificate_sound 15 5 1 cell_15_5_1
    | exact certificate_sound 15 5 2 cell_15_5_2
    | exact certificate_sound 15 5 3 cell_15_5_3
    | exact certificate_sound 15 5 4 cell_15_5_4
    | exact certificate_sound 15 5 5 cell_15_5_5
theorem cell_15_6_0 : CertificateAt 15 6 0 := by decide +kernel
theorem cell_15_6_1 : CertificateAt 15 6 1 := by decide +kernel
theorem cell_15_6_2 : CertificateAt 15 6 2 := by decide +kernel
theorem cell_15_6_3 : CertificateAt 15 6 3 := by decide +kernel
theorem cell_15_6_4 : CertificateAt 15 6 4 := by decide +kernel
theorem cell_15_6_5 : CertificateAt 15 6 5 := by decide +kernel
theorem row_15_6 : ThresholdAt 15 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 6 0 cell_15_6_0
    | exact certificate_sound 15 6 1 cell_15_6_1
    | exact certificate_sound 15 6 2 cell_15_6_2
    | exact certificate_sound 15 6 3 cell_15_6_3
    | exact certificate_sound 15 6 4 cell_15_6_4
    | exact certificate_sound 15 6 5 cell_15_6_5
theorem cell_15_7_0 : CertificateAt 15 7 0 := by decide +kernel
theorem cell_15_7_1 : CertificateAt 15 7 1 := by decide +kernel
theorem cell_15_7_2 : CertificateAt 15 7 2 := by decide +kernel
theorem cell_15_7_3 : CertificateAt 15 7 3 := by decide +kernel
theorem cell_15_7_4 : CertificateAt 15 7 4 := by decide +kernel
theorem cell_15_7_5 : CertificateAt 15 7 5 := by decide +kernel
theorem row_15_7 : ThresholdAt 15 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 7 0 cell_15_7_0
    | exact certificate_sound 15 7 1 cell_15_7_1
    | exact certificate_sound 15 7 2 cell_15_7_2
    | exact certificate_sound 15 7 3 cell_15_7_3
    | exact certificate_sound 15 7 4 cell_15_7_4
    | exact certificate_sound 15 7 5 cell_15_7_5
theorem cell_15_8_0 : CertificateAt 15 8 0 := by decide +kernel
theorem cell_15_8_1 : CertificateAt 15 8 1 := by decide +kernel
theorem cell_15_8_2 : CertificateAt 15 8 2 := by decide +kernel
theorem cell_15_8_3 : CertificateAt 15 8 3 := by decide +kernel
theorem cell_15_8_4 : CertificateAt 15 8 4 := by decide +kernel
theorem cell_15_8_5 : CertificateAt 15 8 5 := by decide +kernel
theorem row_15_8 : ThresholdAt 15 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 8 0 cell_15_8_0
    | exact certificate_sound 15 8 1 cell_15_8_1
    | exact certificate_sound 15 8 2 cell_15_8_2
    | exact certificate_sound 15 8 3 cell_15_8_3
    | exact certificate_sound 15 8 4 cell_15_8_4
    | exact certificate_sound 15 8 5 cell_15_8_5
theorem cell_15_9_0 : CertificateAt 15 9 0 := by decide +kernel
theorem cell_15_9_1 : CertificateAt 15 9 1 := by decide +kernel
theorem cell_15_9_2 : CertificateAt 15 9 2 := by decide +kernel
theorem cell_15_9_3 : CertificateAt 15 9 3 := by decide +kernel
theorem cell_15_9_4 : CertificateAt 15 9 4 := by decide +kernel
theorem cell_15_9_5 : CertificateAt 15 9 5 := by decide +kernel
theorem row_15_9 : ThresholdAt 15 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 9 0 cell_15_9_0
    | exact certificate_sound 15 9 1 cell_15_9_1
    | exact certificate_sound 15 9 2 cell_15_9_2
    | exact certificate_sound 15 9 3 cell_15_9_3
    | exact certificate_sound 15 9 4 cell_15_9_4
    | exact certificate_sound 15 9 5 cell_15_9_5
theorem cell_15_10_0 : CertificateAt 15 10 0 := by decide +kernel
theorem cell_15_10_1 : CertificateAt 15 10 1 := by decide +kernel
theorem cell_15_10_2 : CertificateAt 15 10 2 := by decide +kernel
theorem cell_15_10_3 : CertificateAt 15 10 3 := by decide +kernel
theorem cell_15_10_4 : CertificateAt 15 10 4 := by decide +kernel
theorem cell_15_10_5 : CertificateAt 15 10 5 := by decide +kernel
theorem row_15_10 : ThresholdAt 15 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 10 0 cell_15_10_0
    | exact certificate_sound 15 10 1 cell_15_10_1
    | exact certificate_sound 15 10 2 cell_15_10_2
    | exact certificate_sound 15 10 3 cell_15_10_3
    | exact certificate_sound 15 10 4 cell_15_10_4
    | exact certificate_sound 15 10 5 cell_15_10_5
theorem cell_15_11_0 : CertificateAt 15 11 0 := by decide +kernel
theorem cell_15_11_1 : CertificateAt 15 11 1 := by decide +kernel
theorem cell_15_11_2 : CertificateAt 15 11 2 := by decide +kernel
theorem cell_15_11_3 : CertificateAt 15 11 3 := by decide +kernel
theorem cell_15_11_4 : CertificateAt 15 11 4 := by decide +kernel
theorem cell_15_11_5 : CertificateAt 15 11 5 := by decide +kernel
theorem row_15_11 : ThresholdAt 15 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 11 0 cell_15_11_0
    | exact certificate_sound 15 11 1 cell_15_11_1
    | exact certificate_sound 15 11 2 cell_15_11_2
    | exact certificate_sound 15 11 3 cell_15_11_3
    | exact certificate_sound 15 11 4 cell_15_11_4
    | exact certificate_sound 15 11 5 cell_15_11_5
theorem cell_15_12_0 : CertificateAt 15 12 0 := by decide +kernel
theorem cell_15_12_1 : CertificateAt 15 12 1 := by decide +kernel
theorem cell_15_12_2 : CertificateAt 15 12 2 := by decide +kernel
theorem cell_15_12_3 : CertificateAt 15 12 3 := by decide +kernel
theorem cell_15_12_4 : CertificateAt 15 12 4 := by decide +kernel
theorem cell_15_12_5 : CertificateAt 15 12 5 := by decide +kernel
theorem row_15_12 : ThresholdAt 15 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 12 0 cell_15_12_0
    | exact certificate_sound 15 12 1 cell_15_12_1
    | exact certificate_sound 15 12 2 cell_15_12_2
    | exact certificate_sound 15 12 3 cell_15_12_3
    | exact certificate_sound 15 12 4 cell_15_12_4
    | exact certificate_sound 15 12 5 cell_15_12_5
theorem cell_15_13_0 : CertificateAt 15 13 0 := by decide +kernel
theorem cell_15_13_1 : CertificateAt 15 13 1 := by decide +kernel
theorem cell_15_13_2 : CertificateAt 15 13 2 := by decide +kernel
theorem cell_15_13_3 : CertificateAt 15 13 3 := by decide +kernel
theorem cell_15_13_4 : CertificateAt 15 13 4 := by decide +kernel
theorem cell_15_13_5 : CertificateAt 15 13 5 := by decide +kernel
theorem row_15_13 : ThresholdAt 15 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 13 0 cell_15_13_0
    | exact certificate_sound 15 13 1 cell_15_13_1
    | exact certificate_sound 15 13 2 cell_15_13_2
    | exact certificate_sound 15 13 3 cell_15_13_3
    | exact certificate_sound 15 13 4 cell_15_13_4
    | exact certificate_sound 15 13 5 cell_15_13_5
theorem cell_15_14_0 : CertificateAt 15 14 0 := by decide +kernel
theorem cell_15_14_1 : CertificateAt 15 14 1 := by decide +kernel
theorem cell_15_14_2 : CertificateAt 15 14 2 := by decide +kernel
theorem cell_15_14_3 : CertificateAt 15 14 3 := by decide +kernel
theorem cell_15_14_4 : CertificateAt 15 14 4 := by decide +kernel
theorem cell_15_14_5 : CertificateAt 15 14 5 := by decide +kernel
theorem row_15_14 : ThresholdAt 15 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 14 0 cell_15_14_0
    | exact certificate_sound 15 14 1 cell_15_14_1
    | exact certificate_sound 15 14 2 cell_15_14_2
    | exact certificate_sound 15 14 3 cell_15_14_3
    | exact certificate_sound 15 14 4 cell_15_14_4
    | exact certificate_sound 15 14 5 cell_15_14_5
theorem cell_15_15_0 : CertificateAt 15 15 0 := by decide +kernel
theorem cell_15_15_1 : CertificateAt 15 15 1 := by decide +kernel
theorem cell_15_15_2 : CertificateAt 15 15 2 := by decide +kernel
theorem cell_15_15_3 : CertificateAt 15 15 3 := by decide +kernel
theorem cell_15_15_4 : CertificateAt 15 15 4 := by decide +kernel
theorem cell_15_15_5 : CertificateAt 15 15 5 := by decide +kernel
theorem row_15_15 : ThresholdAt 15 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 15 0 cell_15_15_0
    | exact certificate_sound 15 15 1 cell_15_15_1
    | exact certificate_sound 15 15 2 cell_15_15_2
    | exact certificate_sound 15 15 3 cell_15_15_3
    | exact certificate_sound 15 15 4 cell_15_15_4
    | exact certificate_sound 15 15 5 cell_15_15_5
theorem cell_15_16_0 : CertificateAt 15 16 0 := by decide +kernel
theorem cell_15_16_1 : CertificateAt 15 16 1 := by decide +kernel
theorem cell_15_16_2 : CertificateAt 15 16 2 := by decide +kernel
theorem cell_15_16_3 : CertificateAt 15 16 3 := by decide +kernel
theorem cell_15_16_4 : CertificateAt 15 16 4 := by decide +kernel
theorem cell_15_16_5 : CertificateAt 15 16 5 := by decide +kernel
theorem row_15_16 : ThresholdAt 15 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 16 0 cell_15_16_0
    | exact certificate_sound 15 16 1 cell_15_16_1
    | exact certificate_sound 15 16 2 cell_15_16_2
    | exact certificate_sound 15 16 3 cell_15_16_3
    | exact certificate_sound 15 16 4 cell_15_16_4
    | exact certificate_sound 15 16 5 cell_15_16_5
theorem cell_15_17_0 : CertificateAt 15 17 0 := by decide +kernel
theorem cell_15_17_1 : CertificateAt 15 17 1 := by decide +kernel
theorem cell_15_17_2 : CertificateAt 15 17 2 := by decide +kernel
theorem cell_15_17_3 : CertificateAt 15 17 3 := by decide +kernel
theorem cell_15_17_4 : CertificateAt 15 17 4 := by decide +kernel
theorem cell_15_17_5 : CertificateAt 15 17 5 := by decide +kernel
theorem row_15_17 : ThresholdAt 15 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 17 0 cell_15_17_0
    | exact certificate_sound 15 17 1 cell_15_17_1
    | exact certificate_sound 15 17 2 cell_15_17_2
    | exact certificate_sound 15 17 3 cell_15_17_3
    | exact certificate_sound 15 17 4 cell_15_17_4
    | exact certificate_sound 15 17 5 cell_15_17_5
theorem cell_15_18_0 : CertificateAt 15 18 0 := by decide +kernel
theorem cell_15_18_1 : CertificateAt 15 18 1 := by decide +kernel
theorem cell_15_18_2 : CertificateAt 15 18 2 := by decide +kernel
theorem cell_15_18_3 : CertificateAt 15 18 3 := by decide +kernel
theorem cell_15_18_4 : CertificateAt 15 18 4 := by decide +kernel
theorem cell_15_18_5 : CertificateAt 15 18 5 := by decide +kernel
theorem row_15_18 : ThresholdAt 15 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 18 0 cell_15_18_0
    | exact certificate_sound 15 18 1 cell_15_18_1
    | exact certificate_sound 15 18 2 cell_15_18_2
    | exact certificate_sound 15 18 3 cell_15_18_3
    | exact certificate_sound 15 18 4 cell_15_18_4
    | exact certificate_sound 15 18 5 cell_15_18_5
theorem cell_15_19_0 : CertificateAt 15 19 0 := by decide +kernel
theorem cell_15_19_1 : CertificateAt 15 19 1 := by decide +kernel
theorem cell_15_19_2 : CertificateAt 15 19 2 := by decide +kernel
theorem cell_15_19_3 : CertificateAt 15 19 3 := by decide +kernel
theorem cell_15_19_4 : CertificateAt 15 19 4 := by decide +kernel
theorem cell_15_19_5 : CertificateAt 15 19 5 := by decide +kernel
theorem row_15_19 : ThresholdAt 15 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 19 0 cell_15_19_0
    | exact certificate_sound 15 19 1 cell_15_19_1
    | exact certificate_sound 15 19 2 cell_15_19_2
    | exact certificate_sound 15 19 3 cell_15_19_3
    | exact certificate_sound 15 19 4 cell_15_19_4
    | exact certificate_sound 15 19 5 cell_15_19_5
theorem cell_15_20_0 : CertificateAt 15 20 0 := by decide +kernel
theorem cell_15_20_1 : CertificateAt 15 20 1 := by decide +kernel
theorem cell_15_20_2 : CertificateAt 15 20 2 := by decide +kernel
theorem cell_15_20_3 : CertificateAt 15 20 3 := by decide +kernel
theorem cell_15_20_4 : CertificateAt 15 20 4 := by decide +kernel
theorem cell_15_20_5 : CertificateAt 15 20 5 := by decide +kernel
theorem row_15_20 : ThresholdAt 15 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 20 0 cell_15_20_0
    | exact certificate_sound 15 20 1 cell_15_20_1
    | exact certificate_sound 15 20 2 cell_15_20_2
    | exact certificate_sound 15 20 3 cell_15_20_3
    | exact certificate_sound 15 20 4 cell_15_20_4
    | exact certificate_sound 15 20 5 cell_15_20_5
theorem cell_15_21_0 : CertificateAt 15 21 0 := by decide +kernel
theorem cell_15_21_1 : CertificateAt 15 21 1 := by decide +kernel
theorem cell_15_21_2 : CertificateAt 15 21 2 := by decide +kernel
theorem cell_15_21_3 : CertificateAt 15 21 3 := by decide +kernel
theorem cell_15_21_4 : CertificateAt 15 21 4 := by decide +kernel
theorem cell_15_21_5 : CertificateAt 15 21 5 := by decide +kernel
theorem row_15_21 : ThresholdAt 15 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 21 0 cell_15_21_0
    | exact certificate_sound 15 21 1 cell_15_21_1
    | exact certificate_sound 15 21 2 cell_15_21_2
    | exact certificate_sound 15 21 3 cell_15_21_3
    | exact certificate_sound 15 21 4 cell_15_21_4
    | exact certificate_sound 15 21 5 cell_15_21_5
theorem cell_15_22_0 : CertificateAt 15 22 0 := by decide +kernel
theorem cell_15_22_1 : CertificateAt 15 22 1 := by decide +kernel
theorem cell_15_22_2 : CertificateAt 15 22 2 := by decide +kernel
theorem cell_15_22_3 : CertificateAt 15 22 3 := by decide +kernel
theorem cell_15_22_4 : CertificateAt 15 22 4 := by decide +kernel
theorem cell_15_22_5 : CertificateAt 15 22 5 := by decide +kernel
theorem row_15_22 : ThresholdAt 15 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 22 0 cell_15_22_0
    | exact certificate_sound 15 22 1 cell_15_22_1
    | exact certificate_sound 15 22 2 cell_15_22_2
    | exact certificate_sound 15 22 3 cell_15_22_3
    | exact certificate_sound 15 22 4 cell_15_22_4
    | exact certificate_sound 15 22 5 cell_15_22_5
theorem cell_15_23_0 : CertificateAt 15 23 0 := by decide +kernel
theorem cell_15_23_1 : CertificateAt 15 23 1 := by decide +kernel
theorem cell_15_23_2 : CertificateAt 15 23 2 := by decide +kernel
theorem cell_15_23_3 : CertificateAt 15 23 3 := by decide +kernel
theorem cell_15_23_4 : CertificateAt 15 23 4 := by decide +kernel
theorem cell_15_23_5 : CertificateAt 15 23 5 := by decide +kernel
theorem row_15_23 : ThresholdAt 15 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 23 0 cell_15_23_0
    | exact certificate_sound 15 23 1 cell_15_23_1
    | exact certificate_sound 15 23 2 cell_15_23_2
    | exact certificate_sound 15 23 3 cell_15_23_3
    | exact certificate_sound 15 23 4 cell_15_23_4
    | exact certificate_sound 15 23 5 cell_15_23_5
theorem cell_15_24_0 : CertificateAt 15 24 0 := by decide +kernel
theorem cell_15_24_1 : CertificateAt 15 24 1 := by decide +kernel
theorem cell_15_24_2 : CertificateAt 15 24 2 := by decide +kernel
theorem cell_15_24_3 : CertificateAt 15 24 3 := by decide +kernel
theorem cell_15_24_4 : CertificateAt 15 24 4 := by decide +kernel
theorem cell_15_24_5 : CertificateAt 15 24 5 := by decide +kernel
theorem row_15_24 : ThresholdAt 15 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 24 0 cell_15_24_0
    | exact certificate_sound 15 24 1 cell_15_24_1
    | exact certificate_sound 15 24 2 cell_15_24_2
    | exact certificate_sound 15 24 3 cell_15_24_3
    | exact certificate_sound 15 24 4 cell_15_24_4
    | exact certificate_sound 15 24 5 cell_15_24_5
theorem cell_15_25_0 : CertificateAt 15 25 0 := by decide +kernel
theorem cell_15_25_1 : CertificateAt 15 25 1 := by decide +kernel
theorem cell_15_25_2 : CertificateAt 15 25 2 := by decide +kernel
theorem cell_15_25_3 : CertificateAt 15 25 3 := by decide +kernel
theorem cell_15_25_4 : CertificateAt 15 25 4 := by decide +kernel
theorem cell_15_25_5 : CertificateAt 15 25 5 := by decide +kernel
theorem row_15_25 : ThresholdAt 15 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 25 0 cell_15_25_0
    | exact certificate_sound 15 25 1 cell_15_25_1
    | exact certificate_sound 15 25 2 cell_15_25_2
    | exact certificate_sound 15 25 3 cell_15_25_3
    | exact certificate_sound 15 25 4 cell_15_25_4
    | exact certificate_sound 15 25 5 cell_15_25_5
theorem cell_15_26_0 : CertificateAt 15 26 0 := by decide +kernel
theorem cell_15_26_1 : CertificateAt 15 26 1 := by decide +kernel
theorem cell_15_26_2 : CertificateAt 15 26 2 := by decide +kernel
theorem cell_15_26_3 : CertificateAt 15 26 3 := by decide +kernel
theorem cell_15_26_4 : CertificateAt 15 26 4 := by decide +kernel
theorem cell_15_26_5 : CertificateAt 15 26 5 := by decide +kernel
theorem row_15_26 : ThresholdAt 15 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 26 0 cell_15_26_0
    | exact certificate_sound 15 26 1 cell_15_26_1
    | exact certificate_sound 15 26 2 cell_15_26_2
    | exact certificate_sound 15 26 3 cell_15_26_3
    | exact certificate_sound 15 26 4 cell_15_26_4
    | exact certificate_sound 15 26 5 cell_15_26_5
theorem cell_15_27_0 : CertificateAt 15 27 0 := by decide +kernel
theorem cell_15_27_1 : CertificateAt 15 27 1 := by decide +kernel
theorem cell_15_27_2 : CertificateAt 15 27 2 := by decide +kernel
theorem cell_15_27_3 : CertificateAt 15 27 3 := by decide +kernel
theorem cell_15_27_4 : CertificateAt 15 27 4 := by decide +kernel
theorem cell_15_27_5 : CertificateAt 15 27 5 := by decide +kernel
theorem row_15_27 : ThresholdAt 15 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 27 0 cell_15_27_0
    | exact certificate_sound 15 27 1 cell_15_27_1
    | exact certificate_sound 15 27 2 cell_15_27_2
    | exact certificate_sound 15 27 3 cell_15_27_3
    | exact certificate_sound 15 27 4 cell_15_27_4
    | exact certificate_sound 15 27 5 cell_15_27_5
theorem cell_15_28_0 : CertificateAt 15 28 0 := by decide +kernel
theorem cell_15_28_1 : CertificateAt 15 28 1 := by decide +kernel
theorem cell_15_28_2 : CertificateAt 15 28 2 := by decide +kernel
theorem cell_15_28_3 : CertificateAt 15 28 3 := by decide +kernel
theorem cell_15_28_4 : CertificateAt 15 28 4 := by decide +kernel
theorem cell_15_28_5 : CertificateAt 15 28 5 := by decide +kernel
theorem row_15_28 : ThresholdAt 15 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 28 0 cell_15_28_0
    | exact certificate_sound 15 28 1 cell_15_28_1
    | exact certificate_sound 15 28 2 cell_15_28_2
    | exact certificate_sound 15 28 3 cell_15_28_3
    | exact certificate_sound 15 28 4 cell_15_28_4
    | exact certificate_sound 15 28 5 cell_15_28_5
theorem cell_15_29_0 : CertificateAt 15 29 0 := by decide +kernel
theorem cell_15_29_1 : CertificateAt 15 29 1 := by decide +kernel
theorem cell_15_29_2 : CertificateAt 15 29 2 := by decide +kernel
theorem cell_15_29_3 : CertificateAt 15 29 3 := by decide +kernel
theorem cell_15_29_4 : CertificateAt 15 29 4 := by decide +kernel
theorem cell_15_29_5 : CertificateAt 15 29 5 := by decide +kernel
theorem row_15_29 : ThresholdAt 15 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 29 0 cell_15_29_0
    | exact certificate_sound 15 29 1 cell_15_29_1
    | exact certificate_sound 15 29 2 cell_15_29_2
    | exact certificate_sound 15 29 3 cell_15_29_3
    | exact certificate_sound 15 29 4 cell_15_29_4
    | exact certificate_sound 15 29 5 cell_15_29_5
theorem cell_15_30_0 : CertificateAt 15 30 0 := by decide +kernel
theorem cell_15_30_1 : CertificateAt 15 30 1 := by decide +kernel
theorem cell_15_30_2 : CertificateAt 15 30 2 := by decide +kernel
theorem cell_15_30_3 : CertificateAt 15 30 3 := by decide +kernel
theorem cell_15_30_4 : CertificateAt 15 30 4 := by decide +kernel
theorem cell_15_30_5 : CertificateAt 15 30 5 := by decide +kernel
theorem row_15_30 : ThresholdAt 15 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 30 0 cell_15_30_0
    | exact certificate_sound 15 30 1 cell_15_30_1
    | exact certificate_sound 15 30 2 cell_15_30_2
    | exact certificate_sound 15 30 3 cell_15_30_3
    | exact certificate_sound 15 30 4 cell_15_30_4
    | exact certificate_sound 15 30 5 cell_15_30_5
theorem cell_15_31_0 : CertificateAt 15 31 0 := by decide +kernel
theorem cell_15_31_1 : CertificateAt 15 31 1 := by decide +kernel
theorem cell_15_31_2 : CertificateAt 15 31 2 := by decide +kernel
theorem cell_15_31_3 : CertificateAt 15 31 3 := by decide +kernel
theorem cell_15_31_4 : CertificateAt 15 31 4 := by decide +kernel
theorem cell_15_31_5 : CertificateAt 15 31 5 := by decide +kernel
theorem row_15_31 : ThresholdAt 15 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 31 0 cell_15_31_0
    | exact certificate_sound 15 31 1 cell_15_31_1
    | exact certificate_sound 15 31 2 cell_15_31_2
    | exact certificate_sound 15 31 3 cell_15_31_3
    | exact certificate_sound 15 31 4 cell_15_31_4
    | exact certificate_sound 15 31 5 cell_15_31_5
theorem cell_15_32_0 : CertificateAt 15 32 0 := by decide +kernel
theorem cell_15_32_1 : CertificateAt 15 32 1 := by decide +kernel
theorem cell_15_32_2 : CertificateAt 15 32 2 := by decide +kernel
theorem cell_15_32_3 : CertificateAt 15 32 3 := by decide +kernel
theorem cell_15_32_4 : CertificateAt 15 32 4 := by decide +kernel
theorem cell_15_32_5 : CertificateAt 15 32 5 := by decide +kernel
theorem row_15_32 : ThresholdAt 15 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 32 0 cell_15_32_0
    | exact certificate_sound 15 32 1 cell_15_32_1
    | exact certificate_sound 15 32 2 cell_15_32_2
    | exact certificate_sound 15 32 3 cell_15_32_3
    | exact certificate_sound 15 32 4 cell_15_32_4
    | exact certificate_sound 15 32 5 cell_15_32_5
theorem cell_15_33_0 : CertificateAt 15 33 0 := by decide +kernel
theorem cell_15_33_1 : CertificateAt 15 33 1 := by decide +kernel
theorem cell_15_33_2 : CertificateAt 15 33 2 := by decide +kernel
theorem cell_15_33_3 : CertificateAt 15 33 3 := by decide +kernel
theorem cell_15_33_4 : CertificateAt 15 33 4 := by decide +kernel
theorem cell_15_33_5 : CertificateAt 15 33 5 := by decide +kernel
theorem row_15_33 : ThresholdAt 15 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 33 0 cell_15_33_0
    | exact certificate_sound 15 33 1 cell_15_33_1
    | exact certificate_sound 15 33 2 cell_15_33_2
    | exact certificate_sound 15 33 3 cell_15_33_3
    | exact certificate_sound 15 33 4 cell_15_33_4
    | exact certificate_sound 15 33 5 cell_15_33_5
theorem cell_15_34_0 : CertificateAt 15 34 0 := by decide +kernel
theorem cell_15_34_1 : CertificateAt 15 34 1 := by decide +kernel
theorem cell_15_34_2 : CertificateAt 15 34 2 := by decide +kernel
theorem cell_15_34_3 : CertificateAt 15 34 3 := by decide +kernel
theorem cell_15_34_4 : CertificateAt 15 34 4 := by decide +kernel
theorem cell_15_34_5 : CertificateAt 15 34 5 := by decide +kernel
theorem row_15_34 : ThresholdAt 15 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 34 0 cell_15_34_0
    | exact certificate_sound 15 34 1 cell_15_34_1
    | exact certificate_sound 15 34 2 cell_15_34_2
    | exact certificate_sound 15 34 3 cell_15_34_3
    | exact certificate_sound 15 34 4 cell_15_34_4
    | exact certificate_sound 15 34 5 cell_15_34_5
theorem cell_15_35_0 : CertificateAt 15 35 0 := by decide +kernel
theorem cell_15_35_1 : CertificateAt 15 35 1 := by decide +kernel
theorem cell_15_35_2 : CertificateAt 15 35 2 := by decide +kernel
theorem cell_15_35_3 : CertificateAt 15 35 3 := by decide +kernel
theorem cell_15_35_4 : CertificateAt 15 35 4 := by decide +kernel
theorem cell_15_35_5 : CertificateAt 15 35 5 := by decide +kernel
theorem row_15_35 : ThresholdAt 15 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 35 0 cell_15_35_0
    | exact certificate_sound 15 35 1 cell_15_35_1
    | exact certificate_sound 15 35 2 cell_15_35_2
    | exact certificate_sound 15 35 3 cell_15_35_3
    | exact certificate_sound 15 35 4 cell_15_35_4
    | exact certificate_sound 15 35 5 cell_15_35_5
theorem cell_15_36_0 : CertificateAt 15 36 0 := by decide +kernel
theorem cell_15_36_1 : CertificateAt 15 36 1 := by decide +kernel
theorem cell_15_36_2 : CertificateAt 15 36 2 := by decide +kernel
theorem cell_15_36_3 : CertificateAt 15 36 3 := by decide +kernel
theorem cell_15_36_4 : CertificateAt 15 36 4 := by decide +kernel
theorem cell_15_36_5 : CertificateAt 15 36 5 := by decide +kernel
theorem row_15_36 : ThresholdAt 15 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 36 0 cell_15_36_0
    | exact certificate_sound 15 36 1 cell_15_36_1
    | exact certificate_sound 15 36 2 cell_15_36_2
    | exact certificate_sound 15 36 3 cell_15_36_3
    | exact certificate_sound 15 36 4 cell_15_36_4
    | exact certificate_sound 15 36 5 cell_15_36_5
theorem cell_15_37_0 : CertificateAt 15 37 0 := by decide +kernel
theorem cell_15_37_1 : CertificateAt 15 37 1 := by decide +kernel
theorem cell_15_37_2 : CertificateAt 15 37 2 := by decide +kernel
theorem cell_15_37_3 : CertificateAt 15 37 3 := by decide +kernel
theorem cell_15_37_4 : CertificateAt 15 37 4 := by decide +kernel
theorem cell_15_37_5 : CertificateAt 15 37 5 := by decide +kernel
theorem row_15_37 : ThresholdAt 15 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 37 0 cell_15_37_0
    | exact certificate_sound 15 37 1 cell_15_37_1
    | exact certificate_sound 15 37 2 cell_15_37_2
    | exact certificate_sound 15 37 3 cell_15_37_3
    | exact certificate_sound 15 37 4 cell_15_37_4
    | exact certificate_sound 15 37 5 cell_15_37_5
theorem cell_15_38_0 : CertificateAt 15 38 0 := by decide +kernel
theorem cell_15_38_1 : CertificateAt 15 38 1 := by decide +kernel
theorem cell_15_38_2 : CertificateAt 15 38 2 := by decide +kernel
theorem cell_15_38_3 : CertificateAt 15 38 3 := by decide +kernel
theorem cell_15_38_4 : CertificateAt 15 38 4 := by decide +kernel
theorem cell_15_38_5 : CertificateAt 15 38 5 := by decide +kernel
theorem row_15_38 : ThresholdAt 15 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 38 0 cell_15_38_0
    | exact certificate_sound 15 38 1 cell_15_38_1
    | exact certificate_sound 15 38 2 cell_15_38_2
    | exact certificate_sound 15 38 3 cell_15_38_3
    | exact certificate_sound 15 38 4 cell_15_38_4
    | exact certificate_sound 15 38 5 cell_15_38_5
theorem cell_15_39_0 : CertificateAt 15 39 0 := by decide +kernel
theorem cell_15_39_1 : CertificateAt 15 39 1 := by decide +kernel
theorem cell_15_39_2 : CertificateAt 15 39 2 := by decide +kernel
theorem cell_15_39_3 : CertificateAt 15 39 3 := by decide +kernel
theorem cell_15_39_4 : CertificateAt 15 39 4 := by decide +kernel
theorem cell_15_39_5 : CertificateAt 15 39 5 := by decide +kernel
theorem row_15_39 : ThresholdAt 15 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 39 0 cell_15_39_0
    | exact certificate_sound 15 39 1 cell_15_39_1
    | exact certificate_sound 15 39 2 cell_15_39_2
    | exact certificate_sound 15 39 3 cell_15_39_3
    | exact certificate_sound 15 39 4 cell_15_39_4
    | exact certificate_sound 15 39 5 cell_15_39_5
theorem cell_15_40_0 : CertificateAt 15 40 0 := by decide +kernel
theorem cell_15_40_1 : CertificateAt 15 40 1 := by decide +kernel
theorem cell_15_40_2 : CertificateAt 15 40 2 := by decide +kernel
theorem cell_15_40_3 : CertificateAt 15 40 3 := by decide +kernel
theorem cell_15_40_4 : CertificateAt 15 40 4 := by decide +kernel
theorem cell_15_40_5 : CertificateAt 15 40 5 := by decide +kernel
theorem row_15_40 : ThresholdAt 15 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 40 0 cell_15_40_0
    | exact certificate_sound 15 40 1 cell_15_40_1
    | exact certificate_sound 15 40 2 cell_15_40_2
    | exact certificate_sound 15 40 3 cell_15_40_3
    | exact certificate_sound 15 40 4 cell_15_40_4
    | exact certificate_sound 15 40 5 cell_15_40_5
theorem cell_15_41_0 : CertificateAt 15 41 0 := by decide +kernel
theorem cell_15_41_1 : CertificateAt 15 41 1 := by decide +kernel
theorem cell_15_41_2 : CertificateAt 15 41 2 := by decide +kernel
theorem cell_15_41_3 : CertificateAt 15 41 3 := by decide +kernel
theorem cell_15_41_4 : CertificateAt 15 41 4 := by decide +kernel
theorem cell_15_41_5 : CertificateAt 15 41 5 := by decide +kernel
theorem row_15_41 : ThresholdAt 15 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 41 0 cell_15_41_0
    | exact certificate_sound 15 41 1 cell_15_41_1
    | exact certificate_sound 15 41 2 cell_15_41_2
    | exact certificate_sound 15 41 3 cell_15_41_3
    | exact certificate_sound 15 41 4 cell_15_41_4
    | exact certificate_sound 15 41 5 cell_15_41_5
theorem cell_15_42_0 : CertificateAt 15 42 0 := by decide +kernel
theorem cell_15_42_1 : CertificateAt 15 42 1 := by decide +kernel
theorem cell_15_42_2 : CertificateAt 15 42 2 := by decide +kernel
theorem cell_15_42_3 : CertificateAt 15 42 3 := by decide +kernel
theorem cell_15_42_4 : CertificateAt 15 42 4 := by decide +kernel
theorem cell_15_42_5 : CertificateAt 15 42 5 := by decide +kernel
theorem row_15_42 : ThresholdAt 15 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 42 0 cell_15_42_0
    | exact certificate_sound 15 42 1 cell_15_42_1
    | exact certificate_sound 15 42 2 cell_15_42_2
    | exact certificate_sound 15 42 3 cell_15_42_3
    | exact certificate_sound 15 42 4 cell_15_42_4
    | exact certificate_sound 15 42 5 cell_15_42_5
theorem cell_15_43_0 : CertificateAt 15 43 0 := by decide +kernel
theorem cell_15_43_1 : CertificateAt 15 43 1 := by decide +kernel
theorem cell_15_43_2 : CertificateAt 15 43 2 := by decide +kernel
theorem cell_15_43_3 : CertificateAt 15 43 3 := by decide +kernel
theorem cell_15_43_4 : CertificateAt 15 43 4 := by decide +kernel
theorem cell_15_43_5 : CertificateAt 15 43 5 := by decide +kernel
theorem row_15_43 : ThresholdAt 15 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 43 0 cell_15_43_0
    | exact certificate_sound 15 43 1 cell_15_43_1
    | exact certificate_sound 15 43 2 cell_15_43_2
    | exact certificate_sound 15 43 3 cell_15_43_3
    | exact certificate_sound 15 43 4 cell_15_43_4
    | exact certificate_sound 15 43 5 cell_15_43_5
theorem cell_15_44_0 : CertificateAt 15 44 0 := by decide +kernel
theorem cell_15_44_1 : CertificateAt 15 44 1 := by decide +kernel
theorem cell_15_44_2 : CertificateAt 15 44 2 := by decide +kernel
theorem cell_15_44_3 : CertificateAt 15 44 3 := by decide +kernel
theorem cell_15_44_4 : CertificateAt 15 44 4 := by decide +kernel
theorem cell_15_44_5 : CertificateAt 15 44 5 := by decide +kernel
theorem row_15_44 : ThresholdAt 15 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 44 0 cell_15_44_0
    | exact certificate_sound 15 44 1 cell_15_44_1
    | exact certificate_sound 15 44 2 cell_15_44_2
    | exact certificate_sound 15 44 3 cell_15_44_3
    | exact certificate_sound 15 44 4 cell_15_44_4
    | exact certificate_sound 15 44 5 cell_15_44_5
theorem cell_15_45_0 : CertificateAt 15 45 0 := by decide +kernel
theorem cell_15_45_1 : CertificateAt 15 45 1 := by decide +kernel
theorem cell_15_45_2 : CertificateAt 15 45 2 := by decide +kernel
theorem cell_15_45_3 : CertificateAt 15 45 3 := by decide +kernel
theorem cell_15_45_4 : CertificateAt 15 45 4 := by decide +kernel
theorem cell_15_45_5 : CertificateAt 15 45 5 := by decide +kernel
theorem row_15_45 : ThresholdAt 15 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 45 0 cell_15_45_0
    | exact certificate_sound 15 45 1 cell_15_45_1
    | exact certificate_sound 15 45 2 cell_15_45_2
    | exact certificate_sound 15 45 3 cell_15_45_3
    | exact certificate_sound 15 45 4 cell_15_45_4
    | exact certificate_sound 15 45 5 cell_15_45_5
theorem cell_15_46_0 : CertificateAt 15 46 0 := by decide +kernel
theorem cell_15_46_1 : CertificateAt 15 46 1 := by decide +kernel
theorem cell_15_46_2 : CertificateAt 15 46 2 := by decide +kernel
theorem cell_15_46_3 : CertificateAt 15 46 3 := by decide +kernel
theorem cell_15_46_4 : CertificateAt 15 46 4 := by decide +kernel
theorem cell_15_46_5 : CertificateAt 15 46 5 := by decide +kernel
theorem row_15_46 : ThresholdAt 15 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 46 0 cell_15_46_0
    | exact certificate_sound 15 46 1 cell_15_46_1
    | exact certificate_sound 15 46 2 cell_15_46_2
    | exact certificate_sound 15 46 3 cell_15_46_3
    | exact certificate_sound 15 46 4 cell_15_46_4
    | exact certificate_sound 15 46 5 cell_15_46_5
theorem cell_15_47_0 : CertificateAt 15 47 0 := by decide +kernel
theorem cell_15_47_1 : CertificateAt 15 47 1 := by decide +kernel
theorem cell_15_47_2 : CertificateAt 15 47 2 := by decide +kernel
theorem cell_15_47_3 : CertificateAt 15 47 3 := by decide +kernel
theorem cell_15_47_4 : CertificateAt 15 47 4 := by decide +kernel
theorem cell_15_47_5 : CertificateAt 15 47 5 := by decide +kernel
theorem row_15_47 : ThresholdAt 15 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 47 0 cell_15_47_0
    | exact certificate_sound 15 47 1 cell_15_47_1
    | exact certificate_sound 15 47 2 cell_15_47_2
    | exact certificate_sound 15 47 3 cell_15_47_3
    | exact certificate_sound 15 47 4 cell_15_47_4
    | exact certificate_sound 15 47 5 cell_15_47_5
theorem cell_15_48_0 : CertificateAt 15 48 0 := by decide +kernel
theorem cell_15_48_1 : CertificateAt 15 48 1 := by decide +kernel
theorem cell_15_48_2 : CertificateAt 15 48 2 := by decide +kernel
theorem cell_15_48_3 : CertificateAt 15 48 3 := by decide +kernel
theorem cell_15_48_4 : CertificateAt 15 48 4 := by decide +kernel
theorem cell_15_48_5 : CertificateAt 15 48 5 := by decide +kernel
theorem row_15_48 : ThresholdAt 15 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 48 0 cell_15_48_0
    | exact certificate_sound 15 48 1 cell_15_48_1
    | exact certificate_sound 15 48 2 cell_15_48_2
    | exact certificate_sound 15 48 3 cell_15_48_3
    | exact certificate_sound 15 48 4 cell_15_48_4
    | exact certificate_sound 15 48 5 cell_15_48_5
theorem cell_15_49_0 : CertificateAt 15 49 0 := by decide +kernel
theorem cell_15_49_1 : CertificateAt 15 49 1 := by decide +kernel
theorem cell_15_49_2 : CertificateAt 15 49 2 := by decide +kernel
theorem cell_15_49_3 : CertificateAt 15 49 3 := by decide +kernel
theorem cell_15_49_4 : CertificateAt 15 49 4 := by decide +kernel
theorem cell_15_49_5 : CertificateAt 15 49 5 := by decide +kernel
theorem row_15_49 : ThresholdAt 15 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 49 0 cell_15_49_0
    | exact certificate_sound 15 49 1 cell_15_49_1
    | exact certificate_sound 15 49 2 cell_15_49_2
    | exact certificate_sound 15 49 3 cell_15_49_3
    | exact certificate_sound 15 49 4 cell_15_49_4
    | exact certificate_sound 15 49 5 cell_15_49_5
theorem cell_15_50_0 : CertificateAt 15 50 0 := by decide +kernel
theorem cell_15_50_1 : CertificateAt 15 50 1 := by decide +kernel
theorem cell_15_50_2 : CertificateAt 15 50 2 := by decide +kernel
theorem cell_15_50_3 : CertificateAt 15 50 3 := by decide +kernel
theorem cell_15_50_4 : CertificateAt 15 50 4 := by decide +kernel
theorem cell_15_50_5 : CertificateAt 15 50 5 := by decide +kernel
theorem row_15_50 : ThresholdAt 15 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 50 0 cell_15_50_0
    | exact certificate_sound 15 50 1 cell_15_50_1
    | exact certificate_sound 15 50 2 cell_15_50_2
    | exact certificate_sound 15 50 3 cell_15_50_3
    | exact certificate_sound 15 50 4 cell_15_50_4
    | exact certificate_sound 15 50 5 cell_15_50_5
theorem cell_15_51_0 : CertificateAt 15 51 0 := by decide +kernel
theorem cell_15_51_1 : CertificateAt 15 51 1 := by decide +kernel
theorem cell_15_51_2 : CertificateAt 15 51 2 := by decide +kernel
theorem cell_15_51_3 : CertificateAt 15 51 3 := by decide +kernel
theorem cell_15_51_4 : CertificateAt 15 51 4 := by decide +kernel
theorem cell_15_51_5 : CertificateAt 15 51 5 := by decide +kernel
theorem row_15_51 : ThresholdAt 15 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 51 0 cell_15_51_0
    | exact certificate_sound 15 51 1 cell_15_51_1
    | exact certificate_sound 15 51 2 cell_15_51_2
    | exact certificate_sound 15 51 3 cell_15_51_3
    | exact certificate_sound 15 51 4 cell_15_51_4
    | exact certificate_sound 15 51 5 cell_15_51_5
theorem cell_15_52_0 : CertificateAt 15 52 0 := by decide +kernel
theorem cell_15_52_1 : CertificateAt 15 52 1 := by decide +kernel
theorem cell_15_52_2 : CertificateAt 15 52 2 := by decide +kernel
theorem cell_15_52_3 : CertificateAt 15 52 3 := by decide +kernel
theorem cell_15_52_4 : CertificateAt 15 52 4 := by decide +kernel
theorem cell_15_52_5 : CertificateAt 15 52 5 := by decide +kernel
theorem row_15_52 : ThresholdAt 15 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 52 0 cell_15_52_0
    | exact certificate_sound 15 52 1 cell_15_52_1
    | exact certificate_sound 15 52 2 cell_15_52_2
    | exact certificate_sound 15 52 3 cell_15_52_3
    | exact certificate_sound 15 52 4 cell_15_52_4
    | exact certificate_sound 15 52 5 cell_15_52_5
theorem cell_15_53_0 : CertificateAt 15 53 0 := by decide +kernel
theorem cell_15_53_1 : CertificateAt 15 53 1 := by decide +kernel
theorem cell_15_53_2 : CertificateAt 15 53 2 := by decide +kernel
theorem cell_15_53_3 : CertificateAt 15 53 3 := by decide +kernel
theorem cell_15_53_4 : CertificateAt 15 53 4 := by decide +kernel
theorem cell_15_53_5 : CertificateAt 15 53 5 := by decide +kernel
theorem row_15_53 : ThresholdAt 15 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 53 0 cell_15_53_0
    | exact certificate_sound 15 53 1 cell_15_53_1
    | exact certificate_sound 15 53 2 cell_15_53_2
    | exact certificate_sound 15 53 3 cell_15_53_3
    | exact certificate_sound 15 53 4 cell_15_53_4
    | exact certificate_sound 15 53 5 cell_15_53_5
theorem cell_15_54_0 : CertificateAt 15 54 0 := by decide +kernel
theorem cell_15_54_1 : CertificateAt 15 54 1 := by decide +kernel
theorem cell_15_54_2 : CertificateAt 15 54 2 := by decide +kernel
theorem cell_15_54_3 : CertificateAt 15 54 3 := by decide +kernel
theorem cell_15_54_4 : CertificateAt 15 54 4 := by decide +kernel
theorem cell_15_54_5 : CertificateAt 15 54 5 := by decide +kernel
theorem row_15_54 : ThresholdAt 15 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 54 0 cell_15_54_0
    | exact certificate_sound 15 54 1 cell_15_54_1
    | exact certificate_sound 15 54 2 cell_15_54_2
    | exact certificate_sound 15 54 3 cell_15_54_3
    | exact certificate_sound 15 54 4 cell_15_54_4
    | exact certificate_sound 15 54 5 cell_15_54_5
theorem cell_15_55_0 : CertificateAt 15 55 0 := by decide +kernel
theorem cell_15_55_1 : CertificateAt 15 55 1 := by decide +kernel
theorem cell_15_55_2 : CertificateAt 15 55 2 := by decide +kernel
theorem cell_15_55_3 : CertificateAt 15 55 3 := by decide +kernel
theorem cell_15_55_4 : CertificateAt 15 55 4 := by decide +kernel
theorem cell_15_55_5 : CertificateAt 15 55 5 := by decide +kernel
theorem row_15_55 : ThresholdAt 15 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 55 0 cell_15_55_0
    | exact certificate_sound 15 55 1 cell_15_55_1
    | exact certificate_sound 15 55 2 cell_15_55_2
    | exact certificate_sound 15 55 3 cell_15_55_3
    | exact certificate_sound 15 55 4 cell_15_55_4
    | exact certificate_sound 15 55 5 cell_15_55_5
theorem cell_15_56_0 : CertificateAt 15 56 0 := by decide +kernel
theorem cell_15_56_1 : CertificateAt 15 56 1 := by decide +kernel
theorem cell_15_56_2 : CertificateAt 15 56 2 := by decide +kernel
theorem cell_15_56_3 : CertificateAt 15 56 3 := by decide +kernel
theorem cell_15_56_4 : CertificateAt 15 56 4 := by decide +kernel
theorem cell_15_56_5 : CertificateAt 15 56 5 := by decide +kernel
theorem row_15_56 : ThresholdAt 15 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 56 0 cell_15_56_0
    | exact certificate_sound 15 56 1 cell_15_56_1
    | exact certificate_sound 15 56 2 cell_15_56_2
    | exact certificate_sound 15 56 3 cell_15_56_3
    | exact certificate_sound 15 56 4 cell_15_56_4
    | exact certificate_sound 15 56 5 cell_15_56_5
theorem cell_15_57_0 : CertificateAt 15 57 0 := by decide +kernel
theorem cell_15_57_1 : CertificateAt 15 57 1 := by decide +kernel
theorem cell_15_57_2 : CertificateAt 15 57 2 := by decide +kernel
theorem cell_15_57_3 : CertificateAt 15 57 3 := by decide +kernel
theorem cell_15_57_4 : CertificateAt 15 57 4 := by decide +kernel
theorem cell_15_57_5 : CertificateAt 15 57 5 := by decide +kernel
theorem row_15_57 : ThresholdAt 15 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 57 0 cell_15_57_0
    | exact certificate_sound 15 57 1 cell_15_57_1
    | exact certificate_sound 15 57 2 cell_15_57_2
    | exact certificate_sound 15 57 3 cell_15_57_3
    | exact certificate_sound 15 57 4 cell_15_57_4
    | exact certificate_sound 15 57 5 cell_15_57_5
theorem cell_15_58_0 : CertificateAt 15 58 0 := by decide +kernel
theorem cell_15_58_1 : CertificateAt 15 58 1 := by decide +kernel
theorem cell_15_58_2 : CertificateAt 15 58 2 := by decide +kernel
theorem cell_15_58_3 : CertificateAt 15 58 3 := by decide +kernel
theorem cell_15_58_4 : CertificateAt 15 58 4 := by decide +kernel
theorem cell_15_58_5 : CertificateAt 15 58 5 := by decide +kernel
theorem row_15_58 : ThresholdAt 15 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 58 0 cell_15_58_0
    | exact certificate_sound 15 58 1 cell_15_58_1
    | exact certificate_sound 15 58 2 cell_15_58_2
    | exact certificate_sound 15 58 3 cell_15_58_3
    | exact certificate_sound 15 58 4 cell_15_58_4
    | exact certificate_sound 15 58 5 cell_15_58_5
theorem cell_15_59_0 : CertificateAt 15 59 0 := by decide +kernel
theorem cell_15_59_1 : CertificateAt 15 59 1 := by decide +kernel
theorem cell_15_59_2 : CertificateAt 15 59 2 := by decide +kernel
theorem cell_15_59_3 : CertificateAt 15 59 3 := by decide +kernel
theorem cell_15_59_4 : CertificateAt 15 59 4 := by decide +kernel
theorem cell_15_59_5 : CertificateAt 15 59 5 := by decide +kernel
theorem row_15_59 : ThresholdAt 15 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 59 0 cell_15_59_0
    | exact certificate_sound 15 59 1 cell_15_59_1
    | exact certificate_sound 15 59 2 cell_15_59_2
    | exact certificate_sound 15 59 3 cell_15_59_3
    | exact certificate_sound 15 59 4 cell_15_59_4
    | exact certificate_sound 15 59 5 cell_15_59_5
theorem cell_15_60_0 : CertificateAt 15 60 0 := by decide +kernel
theorem cell_15_60_1 : CertificateAt 15 60 1 := by decide +kernel
theorem cell_15_60_2 : CertificateAt 15 60 2 := by decide +kernel
theorem cell_15_60_3 : CertificateAt 15 60 3 := by decide +kernel
theorem cell_15_60_4 : CertificateAt 15 60 4 := by decide +kernel
theorem cell_15_60_5 : CertificateAt 15 60 5 := by decide +kernel
theorem row_15_60 : ThresholdAt 15 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 60 0 cell_15_60_0
    | exact certificate_sound 15 60 1 cell_15_60_1
    | exact certificate_sound 15 60 2 cell_15_60_2
    | exact certificate_sound 15 60 3 cell_15_60_3
    | exact certificate_sound 15 60 4 cell_15_60_4
    | exact certificate_sound 15 60 5 cell_15_60_5
theorem cell_15_61_0 : CertificateAt 15 61 0 := by decide +kernel
theorem cell_15_61_1 : CertificateAt 15 61 1 := by decide +kernel
theorem cell_15_61_2 : CertificateAt 15 61 2 := by decide +kernel
theorem cell_15_61_3 : CertificateAt 15 61 3 := by decide +kernel
theorem cell_15_61_4 : CertificateAt 15 61 4 := by decide +kernel
theorem cell_15_61_5 : CertificateAt 15 61 5 := by decide +kernel
theorem row_15_61 : ThresholdAt 15 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 61 0 cell_15_61_0
    | exact certificate_sound 15 61 1 cell_15_61_1
    | exact certificate_sound 15 61 2 cell_15_61_2
    | exact certificate_sound 15 61 3 cell_15_61_3
    | exact certificate_sound 15 61 4 cell_15_61_4
    | exact certificate_sound 15 61 5 cell_15_61_5
theorem cell_15_62_0 : CertificateAt 15 62 0 := by decide +kernel
theorem cell_15_62_1 : CertificateAt 15 62 1 := by decide +kernel
theorem cell_15_62_2 : CertificateAt 15 62 2 := by decide +kernel
theorem cell_15_62_3 : CertificateAt 15 62 3 := by decide +kernel
theorem cell_15_62_4 : CertificateAt 15 62 4 := by decide +kernel
theorem cell_15_62_5 : CertificateAt 15 62 5 := by decide +kernel
theorem row_15_62 : ThresholdAt 15 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 62 0 cell_15_62_0
    | exact certificate_sound 15 62 1 cell_15_62_1
    | exact certificate_sound 15 62 2 cell_15_62_2
    | exact certificate_sound 15 62 3 cell_15_62_3
    | exact certificate_sound 15 62 4 cell_15_62_4
    | exact certificate_sound 15 62 5 cell_15_62_5
theorem cell_15_63_0 : CertificateAt 15 63 0 := by decide +kernel
theorem cell_15_63_1 : CertificateAt 15 63 1 := by decide +kernel
theorem cell_15_63_2 : CertificateAt 15 63 2 := by decide +kernel
theorem cell_15_63_3 : CertificateAt 15 63 3 := by decide +kernel
theorem cell_15_63_4 : CertificateAt 15 63 4 := by decide +kernel
theorem cell_15_63_5 : CertificateAt 15 63 5 := by decide +kernel
theorem row_15_63 : ThresholdAt 15 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 63 0 cell_15_63_0
    | exact certificate_sound 15 63 1 cell_15_63_1
    | exact certificate_sound 15 63 2 cell_15_63_2
    | exact certificate_sound 15 63 3 cell_15_63_3
    | exact certificate_sound 15 63 4 cell_15_63_4
    | exact certificate_sound 15 63 5 cell_15_63_5
theorem cell_15_64_0 : CertificateAt 15 64 0 := by decide +kernel
theorem cell_15_64_1 : CertificateAt 15 64 1 := by decide +kernel
theorem cell_15_64_2 : CertificateAt 15 64 2 := by decide +kernel
theorem cell_15_64_3 : CertificateAt 15 64 3 := by decide +kernel
theorem cell_15_64_4 : CertificateAt 15 64 4 := by decide +kernel
theorem cell_15_64_5 : CertificateAt 15 64 5 := by decide +kernel
theorem row_15_64 : ThresholdAt 15 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 64 0 cell_15_64_0
    | exact certificate_sound 15 64 1 cell_15_64_1
    | exact certificate_sound 15 64 2 cell_15_64_2
    | exact certificate_sound 15 64 3 cell_15_64_3
    | exact certificate_sound 15 64 4 cell_15_64_4
    | exact certificate_sound 15 64 5 cell_15_64_5
theorem cell_15_65_0 : CertificateAt 15 65 0 := by decide +kernel
theorem cell_15_65_1 : CertificateAt 15 65 1 := by decide +kernel
theorem cell_15_65_2 : CertificateAt 15 65 2 := by decide +kernel
theorem cell_15_65_3 : CertificateAt 15 65 3 := by decide +kernel
theorem cell_15_65_4 : CertificateAt 15 65 4 := by decide +kernel
theorem cell_15_65_5 : CertificateAt 15 65 5 := by decide +kernel
theorem row_15_65 : ThresholdAt 15 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 65 0 cell_15_65_0
    | exact certificate_sound 15 65 1 cell_15_65_1
    | exact certificate_sound 15 65 2 cell_15_65_2
    | exact certificate_sound 15 65 3 cell_15_65_3
    | exact certificate_sound 15 65 4 cell_15_65_4
    | exact certificate_sound 15 65 5 cell_15_65_5
theorem cell_15_66_0 : CertificateAt 15 66 0 := by decide +kernel
theorem cell_15_66_1 : CertificateAt 15 66 1 := by decide +kernel
theorem cell_15_66_2 : CertificateAt 15 66 2 := by decide +kernel
theorem cell_15_66_3 : CertificateAt 15 66 3 := by decide +kernel
theorem cell_15_66_4 : CertificateAt 15 66 4 := by decide +kernel
theorem cell_15_66_5 : CertificateAt 15 66 5 := by decide +kernel
theorem row_15_66 : ThresholdAt 15 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 66 0 cell_15_66_0
    | exact certificate_sound 15 66 1 cell_15_66_1
    | exact certificate_sound 15 66 2 cell_15_66_2
    | exact certificate_sound 15 66 3 cell_15_66_3
    | exact certificate_sound 15 66 4 cell_15_66_4
    | exact certificate_sound 15 66 5 cell_15_66_5
theorem cell_15_67_0 : CertificateAt 15 67 0 := by decide +kernel
theorem cell_15_67_1 : CertificateAt 15 67 1 := by decide +kernel
theorem cell_15_67_2 : CertificateAt 15 67 2 := by decide +kernel
theorem cell_15_67_3 : CertificateAt 15 67 3 := by decide +kernel
theorem cell_15_67_4 : CertificateAt 15 67 4 := by decide +kernel
theorem cell_15_67_5 : CertificateAt 15 67 5 := by decide +kernel
theorem row_15_67 : ThresholdAt 15 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 67 0 cell_15_67_0
    | exact certificate_sound 15 67 1 cell_15_67_1
    | exact certificate_sound 15 67 2 cell_15_67_2
    | exact certificate_sound 15 67 3 cell_15_67_3
    | exact certificate_sound 15 67 4 cell_15_67_4
    | exact certificate_sound 15 67 5 cell_15_67_5
theorem cell_15_68_0 : CertificateAt 15 68 0 := by decide +kernel
theorem cell_15_68_1 : CertificateAt 15 68 1 := by decide +kernel
theorem cell_15_68_2 : CertificateAt 15 68 2 := by decide +kernel
theorem cell_15_68_3 : CertificateAt 15 68 3 := by decide +kernel
theorem cell_15_68_4 : CertificateAt 15 68 4 := by decide +kernel
theorem cell_15_68_5 : CertificateAt 15 68 5 := by decide +kernel
theorem row_15_68 : ThresholdAt 15 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 68 0 cell_15_68_0
    | exact certificate_sound 15 68 1 cell_15_68_1
    | exact certificate_sound 15 68 2 cell_15_68_2
    | exact certificate_sound 15 68 3 cell_15_68_3
    | exact certificate_sound 15 68 4 cell_15_68_4
    | exact certificate_sound 15 68 5 cell_15_68_5
theorem cell_15_69_0 : CertificateAt 15 69 0 := by decide +kernel
theorem cell_15_69_1 : CertificateAt 15 69 1 := by decide +kernel
theorem cell_15_69_2 : CertificateAt 15 69 2 := by decide +kernel
theorem cell_15_69_3 : CertificateAt 15 69 3 := by decide +kernel
theorem cell_15_69_4 : CertificateAt 15 69 4 := by decide +kernel
theorem cell_15_69_5 : CertificateAt 15 69 5 := by decide +kernel
theorem row_15_69 : ThresholdAt 15 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 69 0 cell_15_69_0
    | exact certificate_sound 15 69 1 cell_15_69_1
    | exact certificate_sound 15 69 2 cell_15_69_2
    | exact certificate_sound 15 69 3 cell_15_69_3
    | exact certificate_sound 15 69 4 cell_15_69_4
    | exact certificate_sound 15 69 5 cell_15_69_5
theorem cell_15_70_0 : CertificateAt 15 70 0 := by decide +kernel
theorem cell_15_70_1 : CertificateAt 15 70 1 := by decide +kernel
theorem cell_15_70_2 : CertificateAt 15 70 2 := by decide +kernel
theorem cell_15_70_3 : CertificateAt 15 70 3 := by decide +kernel
theorem cell_15_70_4 : CertificateAt 15 70 4 := by decide +kernel
theorem cell_15_70_5 : CertificateAt 15 70 5 := by decide +kernel
theorem row_15_70 : ThresholdAt 15 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 70 0 cell_15_70_0
    | exact certificate_sound 15 70 1 cell_15_70_1
    | exact certificate_sound 15 70 2 cell_15_70_2
    | exact certificate_sound 15 70 3 cell_15_70_3
    | exact certificate_sound 15 70 4 cell_15_70_4
    | exact certificate_sound 15 70 5 cell_15_70_5
theorem cell_15_71_0 : CertificateAt 15 71 0 := by decide +kernel
theorem cell_15_71_1 : CertificateAt 15 71 1 := by decide +kernel
theorem cell_15_71_2 : CertificateAt 15 71 2 := by decide +kernel
theorem cell_15_71_3 : CertificateAt 15 71 3 := by decide +kernel
theorem cell_15_71_4 : CertificateAt 15 71 4 := by decide +kernel
theorem cell_15_71_5 : CertificateAt 15 71 5 := by decide +kernel
theorem row_15_71 : ThresholdAt 15 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 71 0 cell_15_71_0
    | exact certificate_sound 15 71 1 cell_15_71_1
    | exact certificate_sound 15 71 2 cell_15_71_2
    | exact certificate_sound 15 71 3 cell_15_71_3
    | exact certificate_sound 15 71 4 cell_15_71_4
    | exact certificate_sound 15 71 5 cell_15_71_5
theorem cell_15_72_0 : CertificateAt 15 72 0 := by decide +kernel
theorem cell_15_72_1 : CertificateAt 15 72 1 := by decide +kernel
theorem cell_15_72_2 : CertificateAt 15 72 2 := by decide +kernel
theorem cell_15_72_3 : CertificateAt 15 72 3 := by decide +kernel
theorem cell_15_72_4 : CertificateAt 15 72 4 := by decide +kernel
theorem cell_15_72_5 : CertificateAt 15 72 5 := by decide +kernel
theorem row_15_72 : ThresholdAt 15 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 72 0 cell_15_72_0
    | exact certificate_sound 15 72 1 cell_15_72_1
    | exact certificate_sound 15 72 2 cell_15_72_2
    | exact certificate_sound 15 72 3 cell_15_72_3
    | exact certificate_sound 15 72 4 cell_15_72_4
    | exact certificate_sound 15 72 5 cell_15_72_5
theorem cell_15_73_0 : CertificateAt 15 73 0 := by decide +kernel
theorem cell_15_73_1 : CertificateAt 15 73 1 := by decide +kernel
theorem cell_15_73_2 : CertificateAt 15 73 2 := by decide +kernel
theorem cell_15_73_3 : CertificateAt 15 73 3 := by decide +kernel
theorem cell_15_73_4 : CertificateAt 15 73 4 := by decide +kernel
theorem cell_15_73_5 : CertificateAt 15 73 5 := by decide +kernel
theorem row_15_73 : ThresholdAt 15 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 73 0 cell_15_73_0
    | exact certificate_sound 15 73 1 cell_15_73_1
    | exact certificate_sound 15 73 2 cell_15_73_2
    | exact certificate_sound 15 73 3 cell_15_73_3
    | exact certificate_sound 15 73 4 cell_15_73_4
    | exact certificate_sound 15 73 5 cell_15_73_5
theorem cell_15_74_0 : CertificateAt 15 74 0 := by decide +kernel
theorem cell_15_74_1 : CertificateAt 15 74 1 := by decide +kernel
theorem cell_15_74_2 : CertificateAt 15 74 2 := by decide +kernel
theorem cell_15_74_3 : CertificateAt 15 74 3 := by decide +kernel
theorem cell_15_74_4 : CertificateAt 15 74 4 := by decide +kernel
theorem cell_15_74_5 : CertificateAt 15 74 5 := by decide +kernel
theorem row_15_74 : ThresholdAt 15 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 74 0 cell_15_74_0
    | exact certificate_sound 15 74 1 cell_15_74_1
    | exact certificate_sound 15 74 2 cell_15_74_2
    | exact certificate_sound 15 74 3 cell_15_74_3
    | exact certificate_sound 15 74 4 cell_15_74_4
    | exact certificate_sound 15 74 5 cell_15_74_5
theorem cell_15_75_0 : CertificateAt 15 75 0 := by decide +kernel
theorem cell_15_75_1 : CertificateAt 15 75 1 := by decide +kernel
theorem cell_15_75_2 : CertificateAt 15 75 2 := by decide +kernel
theorem cell_15_75_3 : CertificateAt 15 75 3 := by decide +kernel
theorem cell_15_75_4 : CertificateAt 15 75 4 := by decide +kernel
theorem cell_15_75_5 : CertificateAt 15 75 5 := by decide +kernel
theorem row_15_75 : ThresholdAt 15 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 75 0 cell_15_75_0
    | exact certificate_sound 15 75 1 cell_15_75_1
    | exact certificate_sound 15 75 2 cell_15_75_2
    | exact certificate_sound 15 75 3 cell_15_75_3
    | exact certificate_sound 15 75 4 cell_15_75_4
    | exact certificate_sound 15 75 5 cell_15_75_5
theorem cell_15_76_0 : CertificateAt 15 76 0 := by decide +kernel
theorem cell_15_76_1 : CertificateAt 15 76 1 := by decide +kernel
theorem cell_15_76_2 : CertificateAt 15 76 2 := by decide +kernel
theorem cell_15_76_3 : CertificateAt 15 76 3 := by decide +kernel
theorem cell_15_76_4 : CertificateAt 15 76 4 := by decide +kernel
theorem cell_15_76_5 : CertificateAt 15 76 5 := by decide +kernel
theorem row_15_76 : ThresholdAt 15 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 76 0 cell_15_76_0
    | exact certificate_sound 15 76 1 cell_15_76_1
    | exact certificate_sound 15 76 2 cell_15_76_2
    | exact certificate_sound 15 76 3 cell_15_76_3
    | exact certificate_sound 15 76 4 cell_15_76_4
    | exact certificate_sound 15 76 5 cell_15_76_5
theorem cell_15_77_0 : CertificateAt 15 77 0 := by decide +kernel
theorem cell_15_77_1 : CertificateAt 15 77 1 := by decide +kernel
theorem cell_15_77_2 : CertificateAt 15 77 2 := by decide +kernel
theorem cell_15_77_3 : CertificateAt 15 77 3 := by decide +kernel
theorem cell_15_77_4 : CertificateAt 15 77 4 := by decide +kernel
theorem cell_15_77_5 : CertificateAt 15 77 5 := by decide +kernel
theorem row_15_77 : ThresholdAt 15 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 77 0 cell_15_77_0
    | exact certificate_sound 15 77 1 cell_15_77_1
    | exact certificate_sound 15 77 2 cell_15_77_2
    | exact certificate_sound 15 77 3 cell_15_77_3
    | exact certificate_sound 15 77 4 cell_15_77_4
    | exact certificate_sound 15 77 5 cell_15_77_5
theorem cell_15_78_0 : CertificateAt 15 78 0 := by decide +kernel
theorem cell_15_78_1 : CertificateAt 15 78 1 := by decide +kernel
theorem cell_15_78_2 : CertificateAt 15 78 2 := by decide +kernel
theorem cell_15_78_3 : CertificateAt 15 78 3 := by decide +kernel
theorem cell_15_78_4 : CertificateAt 15 78 4 := by decide +kernel
theorem cell_15_78_5 : CertificateAt 15 78 5 := by decide +kernel
theorem row_15_78 : ThresholdAt 15 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 78 0 cell_15_78_0
    | exact certificate_sound 15 78 1 cell_15_78_1
    | exact certificate_sound 15 78 2 cell_15_78_2
    | exact certificate_sound 15 78 3 cell_15_78_3
    | exact certificate_sound 15 78 4 cell_15_78_4
    | exact certificate_sound 15 78 5 cell_15_78_5
theorem cell_15_79_0 : CertificateAt 15 79 0 := by decide +kernel
theorem cell_15_79_1 : CertificateAt 15 79 1 := by decide +kernel
theorem cell_15_79_2 : CertificateAt 15 79 2 := by decide +kernel
theorem cell_15_79_3 : CertificateAt 15 79 3 := by decide +kernel
theorem cell_15_79_4 : CertificateAt 15 79 4 := by decide +kernel
theorem cell_15_79_5 : CertificateAt 15 79 5 := by decide +kernel
theorem row_15_79 : ThresholdAt 15 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 79 0 cell_15_79_0
    | exact certificate_sound 15 79 1 cell_15_79_1
    | exact certificate_sound 15 79 2 cell_15_79_2
    | exact certificate_sound 15 79 3 cell_15_79_3
    | exact certificate_sound 15 79 4 cell_15_79_4
    | exact certificate_sound 15 79 5 cell_15_79_5
theorem cell_15_80_0 : CertificateAt 15 80 0 := by decide +kernel
theorem cell_15_80_1 : CertificateAt 15 80 1 := by decide +kernel
theorem cell_15_80_2 : CertificateAt 15 80 2 := by decide +kernel
theorem cell_15_80_3 : CertificateAt 15 80 3 := by decide +kernel
theorem cell_15_80_4 : CertificateAt 15 80 4 := by decide +kernel
theorem cell_15_80_5 : CertificateAt 15 80 5 := by decide +kernel
theorem row_15_80 : ThresholdAt 15 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 80 0 cell_15_80_0
    | exact certificate_sound 15 80 1 cell_15_80_1
    | exact certificate_sound 15 80 2 cell_15_80_2
    | exact certificate_sound 15 80 3 cell_15_80_3
    | exact certificate_sound 15 80 4 cell_15_80_4
    | exact certificate_sound 15 80 5 cell_15_80_5
theorem cell_15_81_0 : CertificateAt 15 81 0 := by decide +kernel
theorem cell_15_81_1 : CertificateAt 15 81 1 := by decide +kernel
theorem cell_15_81_2 : CertificateAt 15 81 2 := by decide +kernel
theorem cell_15_81_3 : CertificateAt 15 81 3 := by decide +kernel
theorem cell_15_81_4 : CertificateAt 15 81 4 := by decide +kernel
theorem cell_15_81_5 : CertificateAt 15 81 5 := by decide +kernel
theorem row_15_81 : ThresholdAt 15 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 81 0 cell_15_81_0
    | exact certificate_sound 15 81 1 cell_15_81_1
    | exact certificate_sound 15 81 2 cell_15_81_2
    | exact certificate_sound 15 81 3 cell_15_81_3
    | exact certificate_sound 15 81 4 cell_15_81_4
    | exact certificate_sound 15 81 5 cell_15_81_5
theorem cell_15_82_0 : CertificateAt 15 82 0 := by decide +kernel
theorem cell_15_82_1 : CertificateAt 15 82 1 := by decide +kernel
theorem cell_15_82_2 : CertificateAt 15 82 2 := by decide +kernel
theorem cell_15_82_3 : CertificateAt 15 82 3 := by decide +kernel
theorem cell_15_82_4 : CertificateAt 15 82 4 := by decide +kernel
theorem cell_15_82_5 : CertificateAt 15 82 5 := by decide +kernel
theorem row_15_82 : ThresholdAt 15 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 82 0 cell_15_82_0
    | exact certificate_sound 15 82 1 cell_15_82_1
    | exact certificate_sound 15 82 2 cell_15_82_2
    | exact certificate_sound 15 82 3 cell_15_82_3
    | exact certificate_sound 15 82 4 cell_15_82_4
    | exact certificate_sound 15 82 5 cell_15_82_5
theorem cell_15_83_0 : CertificateAt 15 83 0 := by decide +kernel
theorem cell_15_83_1 : CertificateAt 15 83 1 := by decide +kernel
theorem cell_15_83_2 : CertificateAt 15 83 2 := by decide +kernel
theorem cell_15_83_3 : CertificateAt 15 83 3 := by decide +kernel
theorem cell_15_83_4 : CertificateAt 15 83 4 := by decide +kernel
theorem cell_15_83_5 : CertificateAt 15 83 5 := by decide +kernel
theorem row_15_83 : ThresholdAt 15 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 83 0 cell_15_83_0
    | exact certificate_sound 15 83 1 cell_15_83_1
    | exact certificate_sound 15 83 2 cell_15_83_2
    | exact certificate_sound 15 83 3 cell_15_83_3
    | exact certificate_sound 15 83 4 cell_15_83_4
    | exact certificate_sound 15 83 5 cell_15_83_5
theorem cell_15_84_0 : CertificateAt 15 84 0 := by decide +kernel
theorem cell_15_84_1 : CertificateAt 15 84 1 := by decide +kernel
theorem cell_15_84_2 : CertificateAt 15 84 2 := by decide +kernel
theorem cell_15_84_3 : CertificateAt 15 84 3 := by decide +kernel
theorem cell_15_84_4 : CertificateAt 15 84 4 := by decide +kernel
theorem cell_15_84_5 : CertificateAt 15 84 5 := by decide +kernel
theorem row_15_84 : ThresholdAt 15 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 84 0 cell_15_84_0
    | exact certificate_sound 15 84 1 cell_15_84_1
    | exact certificate_sound 15 84 2 cell_15_84_2
    | exact certificate_sound 15 84 3 cell_15_84_3
    | exact certificate_sound 15 84 4 cell_15_84_4
    | exact certificate_sound 15 84 5 cell_15_84_5
theorem cell_15_85_0 : CertificateAt 15 85 0 := by decide +kernel
theorem cell_15_85_1 : CertificateAt 15 85 1 := by decide +kernel
theorem cell_15_85_2 : CertificateAt 15 85 2 := by decide +kernel
theorem cell_15_85_3 : CertificateAt 15 85 3 := by decide +kernel
theorem cell_15_85_4 : CertificateAt 15 85 4 := by decide +kernel
theorem cell_15_85_5 : CertificateAt 15 85 5 := by decide +kernel
theorem row_15_85 : ThresholdAt 15 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 85 0 cell_15_85_0
    | exact certificate_sound 15 85 1 cell_15_85_1
    | exact certificate_sound 15 85 2 cell_15_85_2
    | exact certificate_sound 15 85 3 cell_15_85_3
    | exact certificate_sound 15 85 4 cell_15_85_4
    | exact certificate_sound 15 85 5 cell_15_85_5
theorem cell_15_86_0 : CertificateAt 15 86 0 := by decide +kernel
theorem cell_15_86_1 : CertificateAt 15 86 1 := by decide +kernel
theorem cell_15_86_2 : CertificateAt 15 86 2 := by decide +kernel
theorem cell_15_86_3 : CertificateAt 15 86 3 := by decide +kernel
theorem cell_15_86_4 : CertificateAt 15 86 4 := by decide +kernel
theorem cell_15_86_5 : CertificateAt 15 86 5 := by decide +kernel
theorem row_15_86 : ThresholdAt 15 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 86 0 cell_15_86_0
    | exact certificate_sound 15 86 1 cell_15_86_1
    | exact certificate_sound 15 86 2 cell_15_86_2
    | exact certificate_sound 15 86 3 cell_15_86_3
    | exact certificate_sound 15 86 4 cell_15_86_4
    | exact certificate_sound 15 86 5 cell_15_86_5
theorem cell_15_87_0 : CertificateAt 15 87 0 := by decide +kernel
theorem cell_15_87_1 : CertificateAt 15 87 1 := by decide +kernel
theorem cell_15_87_2 : CertificateAt 15 87 2 := by decide +kernel
theorem cell_15_87_3 : CertificateAt 15 87 3 := by decide +kernel
theorem cell_15_87_4 : CertificateAt 15 87 4 := by decide +kernel
theorem cell_15_87_5 : CertificateAt 15 87 5 := by decide +kernel
theorem row_15_87 : ThresholdAt 15 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 87 0 cell_15_87_0
    | exact certificate_sound 15 87 1 cell_15_87_1
    | exact certificate_sound 15 87 2 cell_15_87_2
    | exact certificate_sound 15 87 3 cell_15_87_3
    | exact certificate_sound 15 87 4 cell_15_87_4
    | exact certificate_sound 15 87 5 cell_15_87_5
theorem cell_15_88_0 : CertificateAt 15 88 0 := by decide +kernel
theorem cell_15_88_1 : CertificateAt 15 88 1 := by decide +kernel
theorem cell_15_88_2 : CertificateAt 15 88 2 := by decide +kernel
theorem cell_15_88_3 : CertificateAt 15 88 3 := by decide +kernel
theorem cell_15_88_4 : CertificateAt 15 88 4 := by decide +kernel
theorem cell_15_88_5 : CertificateAt 15 88 5 := by decide +kernel
theorem row_15_88 : ThresholdAt 15 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 88 0 cell_15_88_0
    | exact certificate_sound 15 88 1 cell_15_88_1
    | exact certificate_sound 15 88 2 cell_15_88_2
    | exact certificate_sound 15 88 3 cell_15_88_3
    | exact certificate_sound 15 88 4 cell_15_88_4
    | exact certificate_sound 15 88 5 cell_15_88_5
theorem cell_15_89_0 : CertificateAt 15 89 0 := by decide +kernel
theorem cell_15_89_1 : CertificateAt 15 89 1 := by decide +kernel
theorem cell_15_89_2 : CertificateAt 15 89 2 := by decide +kernel
theorem cell_15_89_3 : CertificateAt 15 89 3 := by decide +kernel
theorem cell_15_89_4 : CertificateAt 15 89 4 := by decide +kernel
theorem cell_15_89_5 : CertificateAt 15 89 5 := by decide +kernel
theorem row_15_89 : ThresholdAt 15 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 89 0 cell_15_89_0
    | exact certificate_sound 15 89 1 cell_15_89_1
    | exact certificate_sound 15 89 2 cell_15_89_2
    | exact certificate_sound 15 89 3 cell_15_89_3
    | exact certificate_sound 15 89 4 cell_15_89_4
    | exact certificate_sound 15 89 5 cell_15_89_5
theorem cell_15_90_0 : CertificateAt 15 90 0 := by decide +kernel
theorem cell_15_90_1 : CertificateAt 15 90 1 := by decide +kernel
theorem cell_15_90_2 : CertificateAt 15 90 2 := by decide +kernel
theorem cell_15_90_3 : CertificateAt 15 90 3 := by decide +kernel
theorem cell_15_90_4 : CertificateAt 15 90 4 := by decide +kernel
theorem cell_15_90_5 : CertificateAt 15 90 5 := by decide +kernel
theorem row_15_90 : ThresholdAt 15 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 90 0 cell_15_90_0
    | exact certificate_sound 15 90 1 cell_15_90_1
    | exact certificate_sound 15 90 2 cell_15_90_2
    | exact certificate_sound 15 90 3 cell_15_90_3
    | exact certificate_sound 15 90 4 cell_15_90_4
    | exact certificate_sound 15 90 5 cell_15_90_5
theorem cell_15_91_0 : CertificateAt 15 91 0 := by decide +kernel
theorem cell_15_91_1 : CertificateAt 15 91 1 := by decide +kernel
theorem cell_15_91_2 : CertificateAt 15 91 2 := by decide +kernel
theorem cell_15_91_3 : CertificateAt 15 91 3 := by decide +kernel
theorem cell_15_91_4 : CertificateAt 15 91 4 := by decide +kernel
theorem cell_15_91_5 : CertificateAt 15 91 5 := by decide +kernel
theorem row_15_91 : ThresholdAt 15 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 91 0 cell_15_91_0
    | exact certificate_sound 15 91 1 cell_15_91_1
    | exact certificate_sound 15 91 2 cell_15_91_2
    | exact certificate_sound 15 91 3 cell_15_91_3
    | exact certificate_sound 15 91 4 cell_15_91_4
    | exact certificate_sound 15 91 5 cell_15_91_5
theorem cell_15_92_0 : CertificateAt 15 92 0 := by decide +kernel
theorem cell_15_92_1 : CertificateAt 15 92 1 := by decide +kernel
theorem cell_15_92_2 : CertificateAt 15 92 2 := by decide +kernel
theorem cell_15_92_3 : CertificateAt 15 92 3 := by decide +kernel
theorem cell_15_92_4 : CertificateAt 15 92 4 := by decide +kernel
theorem cell_15_92_5 : CertificateAt 15 92 5 := by decide +kernel
theorem row_15_92 : ThresholdAt 15 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 92 0 cell_15_92_0
    | exact certificate_sound 15 92 1 cell_15_92_1
    | exact certificate_sound 15 92 2 cell_15_92_2
    | exact certificate_sound 15 92 3 cell_15_92_3
    | exact certificate_sound 15 92 4 cell_15_92_4
    | exact certificate_sound 15 92 5 cell_15_92_5
theorem cell_15_93_0 : CertificateAt 15 93 0 := by decide +kernel
theorem cell_15_93_1 : CertificateAt 15 93 1 := by decide +kernel
theorem cell_15_93_2 : CertificateAt 15 93 2 := by decide +kernel
theorem cell_15_93_3 : CertificateAt 15 93 3 := by decide +kernel
theorem cell_15_93_4 : CertificateAt 15 93 4 := by decide +kernel
theorem cell_15_93_5 : CertificateAt 15 93 5 := by decide +kernel
theorem row_15_93 : ThresholdAt 15 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 93 0 cell_15_93_0
    | exact certificate_sound 15 93 1 cell_15_93_1
    | exact certificate_sound 15 93 2 cell_15_93_2
    | exact certificate_sound 15 93 3 cell_15_93_3
    | exact certificate_sound 15 93 4 cell_15_93_4
    | exact certificate_sound 15 93 5 cell_15_93_5
theorem cell_15_94_0 : CertificateAt 15 94 0 := by decide +kernel
theorem cell_15_94_1 : CertificateAt 15 94 1 := by decide +kernel
theorem cell_15_94_2 : CertificateAt 15 94 2 := by decide +kernel
theorem cell_15_94_3 : CertificateAt 15 94 3 := by decide +kernel
theorem cell_15_94_4 : CertificateAt 15 94 4 := by decide +kernel
theorem cell_15_94_5 : CertificateAt 15 94 5 := by decide +kernel
theorem row_15_94 : ThresholdAt 15 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 94 0 cell_15_94_0
    | exact certificate_sound 15 94 1 cell_15_94_1
    | exact certificate_sound 15 94 2 cell_15_94_2
    | exact certificate_sound 15 94 3 cell_15_94_3
    | exact certificate_sound 15 94 4 cell_15_94_4
    | exact certificate_sound 15 94 5 cell_15_94_5
theorem cell_15_95_0 : CertificateAt 15 95 0 := by decide +kernel
theorem cell_15_95_1 : CertificateAt 15 95 1 := by decide +kernel
theorem cell_15_95_2 : CertificateAt 15 95 2 := by decide +kernel
theorem cell_15_95_3 : CertificateAt 15 95 3 := by decide +kernel
theorem cell_15_95_4 : CertificateAt 15 95 4 := by decide +kernel
theorem cell_15_95_5 : CertificateAt 15 95 5 := by decide +kernel
theorem row_15_95 : ThresholdAt 15 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 95 0 cell_15_95_0
    | exact certificate_sound 15 95 1 cell_15_95_1
    | exact certificate_sound 15 95 2 cell_15_95_2
    | exact certificate_sound 15 95 3 cell_15_95_3
    | exact certificate_sound 15 95 4 cell_15_95_4
    | exact certificate_sound 15 95 5 cell_15_95_5
theorem cell_15_96_0 : CertificateAt 15 96 0 := by decide +kernel
theorem cell_15_96_1 : CertificateAt 15 96 1 := by decide +kernel
theorem cell_15_96_2 : CertificateAt 15 96 2 := by decide +kernel
theorem cell_15_96_3 : CertificateAt 15 96 3 := by decide +kernel
theorem cell_15_96_4 : CertificateAt 15 96 4 := by decide +kernel
theorem cell_15_96_5 : CertificateAt 15 96 5 := by decide +kernel
theorem row_15_96 : ThresholdAt 15 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 96 0 cell_15_96_0
    | exact certificate_sound 15 96 1 cell_15_96_1
    | exact certificate_sound 15 96 2 cell_15_96_2
    | exact certificate_sound 15 96 3 cell_15_96_3
    | exact certificate_sound 15 96 4 cell_15_96_4
    | exact certificate_sound 15 96 5 cell_15_96_5
theorem cell_15_97_0 : CertificateAt 15 97 0 := by decide +kernel
theorem cell_15_97_1 : CertificateAt 15 97 1 := by decide +kernel
theorem cell_15_97_2 : CertificateAt 15 97 2 := by decide +kernel
theorem cell_15_97_3 : CertificateAt 15 97 3 := by decide +kernel
theorem cell_15_97_4 : CertificateAt 15 97 4 := by decide +kernel
theorem cell_15_97_5 : CertificateAt 15 97 5 := by decide +kernel
theorem row_15_97 : ThresholdAt 15 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 97 0 cell_15_97_0
    | exact certificate_sound 15 97 1 cell_15_97_1
    | exact certificate_sound 15 97 2 cell_15_97_2
    | exact certificate_sound 15 97 3 cell_15_97_3
    | exact certificate_sound 15 97 4 cell_15_97_4
    | exact certificate_sound 15 97 5 cell_15_97_5
theorem cell_15_98_0 : CertificateAt 15 98 0 := by decide +kernel
theorem cell_15_98_1 : CertificateAt 15 98 1 := by decide +kernel
theorem cell_15_98_2 : CertificateAt 15 98 2 := by decide +kernel
theorem cell_15_98_3 : CertificateAt 15 98 3 := by decide +kernel
theorem cell_15_98_4 : CertificateAt 15 98 4 := by decide +kernel
theorem cell_15_98_5 : CertificateAt 15 98 5 := by decide +kernel
theorem row_15_98 : ThresholdAt 15 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 98 0 cell_15_98_0
    | exact certificate_sound 15 98 1 cell_15_98_1
    | exact certificate_sound 15 98 2 cell_15_98_2
    | exact certificate_sound 15 98 3 cell_15_98_3
    | exact certificate_sound 15 98 4 cell_15_98_4
    | exact certificate_sound 15 98 5 cell_15_98_5
theorem cell_15_99_0 : CertificateAt 15 99 0 := by decide +kernel
theorem cell_15_99_1 : CertificateAt 15 99 1 := by decide +kernel
theorem cell_15_99_2 : CertificateAt 15 99 2 := by decide +kernel
theorem cell_15_99_3 : CertificateAt 15 99 3 := by decide +kernel
theorem cell_15_99_4 : CertificateAt 15 99 4 := by decide +kernel
theorem cell_15_99_5 : CertificateAt 15 99 5 := by decide +kernel
theorem row_15_99 : ThresholdAt 15 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 99 0 cell_15_99_0
    | exact certificate_sound 15 99 1 cell_15_99_1
    | exact certificate_sound 15 99 2 cell_15_99_2
    | exact certificate_sound 15 99 3 cell_15_99_3
    | exact certificate_sound 15 99 4 cell_15_99_4
    | exact certificate_sound 15 99 5 cell_15_99_5
theorem cell_15_100_0 : CertificateAt 15 100 0 := by decide +kernel
theorem cell_15_100_1 : CertificateAt 15 100 1 := by decide +kernel
theorem cell_15_100_2 : CertificateAt 15 100 2 := by decide +kernel
theorem cell_15_100_3 : CertificateAt 15 100 3 := by decide +kernel
theorem cell_15_100_4 : CertificateAt 15 100 4 := by decide +kernel
theorem cell_15_100_5 : CertificateAt 15 100 5 := by decide +kernel
theorem row_15_100 : ThresholdAt 15 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 100 0 cell_15_100_0
    | exact certificate_sound 15 100 1 cell_15_100_1
    | exact certificate_sound 15 100 2 cell_15_100_2
    | exact certificate_sound 15 100 3 cell_15_100_3
    | exact certificate_sound 15 100 4 cell_15_100_4
    | exact certificate_sound 15 100 5 cell_15_100_5
theorem cell_15_101_0 : CertificateAt 15 101 0 := by decide +kernel
theorem cell_15_101_1 : CertificateAt 15 101 1 := by decide +kernel
theorem cell_15_101_2 : CertificateAt 15 101 2 := by decide +kernel
theorem cell_15_101_3 : CertificateAt 15 101 3 := by decide +kernel
theorem cell_15_101_4 : CertificateAt 15 101 4 := by decide +kernel
theorem cell_15_101_5 : CertificateAt 15 101 5 := by decide +kernel
theorem row_15_101 : ThresholdAt 15 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 101 0 cell_15_101_0
    | exact certificate_sound 15 101 1 cell_15_101_1
    | exact certificate_sound 15 101 2 cell_15_101_2
    | exact certificate_sound 15 101 3 cell_15_101_3
    | exact certificate_sound 15 101 4 cell_15_101_4
    | exact certificate_sound 15 101 5 cell_15_101_5
theorem cell_15_102_0 : CertificateAt 15 102 0 := by decide +kernel
theorem cell_15_102_1 : CertificateAt 15 102 1 := by decide +kernel
theorem cell_15_102_2 : CertificateAt 15 102 2 := by decide +kernel
theorem cell_15_102_3 : CertificateAt 15 102 3 := by decide +kernel
theorem cell_15_102_4 : CertificateAt 15 102 4 := by decide +kernel
theorem cell_15_102_5 : CertificateAt 15 102 5 := by decide +kernel
theorem row_15_102 : ThresholdAt 15 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 102 0 cell_15_102_0
    | exact certificate_sound 15 102 1 cell_15_102_1
    | exact certificate_sound 15 102 2 cell_15_102_2
    | exact certificate_sound 15 102 3 cell_15_102_3
    | exact certificate_sound 15 102 4 cell_15_102_4
    | exact certificate_sound 15 102 5 cell_15_102_5
theorem cell_15_103_0 : CertificateAt 15 103 0 := by decide +kernel
theorem cell_15_103_1 : CertificateAt 15 103 1 := by decide +kernel
theorem cell_15_103_2 : CertificateAt 15 103 2 := by decide +kernel
theorem cell_15_103_3 : CertificateAt 15 103 3 := by decide +kernel
theorem cell_15_103_4 : CertificateAt 15 103 4 := by decide +kernel
theorem cell_15_103_5 : CertificateAt 15 103 5 := by decide +kernel
theorem row_15_103 : ThresholdAt 15 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 103 0 cell_15_103_0
    | exact certificate_sound 15 103 1 cell_15_103_1
    | exact certificate_sound 15 103 2 cell_15_103_2
    | exact certificate_sound 15 103 3 cell_15_103_3
    | exact certificate_sound 15 103 4 cell_15_103_4
    | exact certificate_sound 15 103 5 cell_15_103_5
theorem cell_15_104_0 : CertificateAt 15 104 0 := by decide +kernel
theorem cell_15_104_1 : CertificateAt 15 104 1 := by decide +kernel
theorem cell_15_104_2 : CertificateAt 15 104 2 := by decide +kernel
theorem cell_15_104_3 : CertificateAt 15 104 3 := by decide +kernel
theorem cell_15_104_4 : CertificateAt 15 104 4 := by decide +kernel
theorem cell_15_104_5 : CertificateAt 15 104 5 := by decide +kernel
theorem row_15_104 : ThresholdAt 15 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 104 0 cell_15_104_0
    | exact certificate_sound 15 104 1 cell_15_104_1
    | exact certificate_sound 15 104 2 cell_15_104_2
    | exact certificate_sound 15 104 3 cell_15_104_3
    | exact certificate_sound 15 104 4 cell_15_104_4
    | exact certificate_sound 15 104 5 cell_15_104_5
theorem cell_15_105_0 : CertificateAt 15 105 0 := by decide +kernel
theorem cell_15_105_1 : CertificateAt 15 105 1 := by decide +kernel
theorem cell_15_105_2 : CertificateAt 15 105 2 := by decide +kernel
theorem cell_15_105_3 : CertificateAt 15 105 3 := by decide +kernel
theorem cell_15_105_4 : CertificateAt 15 105 4 := by decide +kernel
theorem cell_15_105_5 : CertificateAt 15 105 5 := by decide +kernel
theorem row_15_105 : ThresholdAt 15 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 105 0 cell_15_105_0
    | exact certificate_sound 15 105 1 cell_15_105_1
    | exact certificate_sound 15 105 2 cell_15_105_2
    | exact certificate_sound 15 105 3 cell_15_105_3
    | exact certificate_sound 15 105 4 cell_15_105_4
    | exact certificate_sound 15 105 5 cell_15_105_5
theorem cell_15_106_0 : CertificateAt 15 106 0 := by decide +kernel
theorem cell_15_106_1 : CertificateAt 15 106 1 := by decide +kernel
theorem cell_15_106_2 : CertificateAt 15 106 2 := by decide +kernel
theorem cell_15_106_3 : CertificateAt 15 106 3 := by decide +kernel
theorem cell_15_106_4 : CertificateAt 15 106 4 := by decide +kernel
theorem cell_15_106_5 : CertificateAt 15 106 5 := by decide +kernel
theorem row_15_106 : ThresholdAt 15 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 106 0 cell_15_106_0
    | exact certificate_sound 15 106 1 cell_15_106_1
    | exact certificate_sound 15 106 2 cell_15_106_2
    | exact certificate_sound 15 106 3 cell_15_106_3
    | exact certificate_sound 15 106 4 cell_15_106_4
    | exact certificate_sound 15 106 5 cell_15_106_5
theorem cell_15_107_0 : CertificateAt 15 107 0 := by decide +kernel
theorem cell_15_107_1 : CertificateAt 15 107 1 := by decide +kernel
theorem cell_15_107_2 : CertificateAt 15 107 2 := by decide +kernel
theorem cell_15_107_3 : CertificateAt 15 107 3 := by decide +kernel
theorem cell_15_107_4 : CertificateAt 15 107 4 := by decide +kernel
theorem cell_15_107_5 : CertificateAt 15 107 5 := by decide +kernel
theorem row_15_107 : ThresholdAt 15 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 107 0 cell_15_107_0
    | exact certificate_sound 15 107 1 cell_15_107_1
    | exact certificate_sound 15 107 2 cell_15_107_2
    | exact certificate_sound 15 107 3 cell_15_107_3
    | exact certificate_sound 15 107 4 cell_15_107_4
    | exact certificate_sound 15 107 5 cell_15_107_5
theorem cell_15_108_0 : CertificateAt 15 108 0 := by decide +kernel
theorem cell_15_108_1 : CertificateAt 15 108 1 := by decide +kernel
theorem cell_15_108_2 : CertificateAt 15 108 2 := by decide +kernel
theorem cell_15_108_3 : CertificateAt 15 108 3 := by decide +kernel
theorem cell_15_108_4 : CertificateAt 15 108 4 := by decide +kernel
theorem cell_15_108_5 : CertificateAt 15 108 5 := by decide +kernel
theorem row_15_108 : ThresholdAt 15 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 108 0 cell_15_108_0
    | exact certificate_sound 15 108 1 cell_15_108_1
    | exact certificate_sound 15 108 2 cell_15_108_2
    | exact certificate_sound 15 108 3 cell_15_108_3
    | exact certificate_sound 15 108 4 cell_15_108_4
    | exact certificate_sound 15 108 5 cell_15_108_5
theorem cell_15_109_0 : CertificateAt 15 109 0 := by decide +kernel
theorem cell_15_109_1 : CertificateAt 15 109 1 := by decide +kernel
theorem cell_15_109_2 : CertificateAt 15 109 2 := by decide +kernel
theorem cell_15_109_3 : CertificateAt 15 109 3 := by decide +kernel
theorem cell_15_109_4 : CertificateAt 15 109 4 := by decide +kernel
theorem cell_15_109_5 : CertificateAt 15 109 5 := by decide +kernel
theorem row_15_109 : ThresholdAt 15 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 109 0 cell_15_109_0
    | exact certificate_sound 15 109 1 cell_15_109_1
    | exact certificate_sound 15 109 2 cell_15_109_2
    | exact certificate_sound 15 109 3 cell_15_109_3
    | exact certificate_sound 15 109 4 cell_15_109_4
    | exact certificate_sound 15 109 5 cell_15_109_5
theorem cell_15_110_0 : CertificateAt 15 110 0 := by decide +kernel
theorem cell_15_110_1 : CertificateAt 15 110 1 := by decide +kernel
theorem cell_15_110_2 : CertificateAt 15 110 2 := by decide +kernel
theorem cell_15_110_3 : CertificateAt 15 110 3 := by decide +kernel
theorem cell_15_110_4 : CertificateAt 15 110 4 := by decide +kernel
theorem cell_15_110_5 : CertificateAt 15 110 5 := by decide +kernel
theorem row_15_110 : ThresholdAt 15 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 110 0 cell_15_110_0
    | exact certificate_sound 15 110 1 cell_15_110_1
    | exact certificate_sound 15 110 2 cell_15_110_2
    | exact certificate_sound 15 110 3 cell_15_110_3
    | exact certificate_sound 15 110 4 cell_15_110_4
    | exact certificate_sound 15 110 5 cell_15_110_5
theorem cell_15_111_0 : CertificateAt 15 111 0 := by decide +kernel
theorem cell_15_111_1 : CertificateAt 15 111 1 := by decide +kernel
theorem cell_15_111_2 : CertificateAt 15 111 2 := by decide +kernel
theorem cell_15_111_3 : CertificateAt 15 111 3 := by decide +kernel
theorem cell_15_111_4 : CertificateAt 15 111 4 := by decide +kernel
theorem cell_15_111_5 : CertificateAt 15 111 5 := by decide +kernel
theorem row_15_111 : ThresholdAt 15 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 111 0 cell_15_111_0
    | exact certificate_sound 15 111 1 cell_15_111_1
    | exact certificate_sound 15 111 2 cell_15_111_2
    | exact certificate_sound 15 111 3 cell_15_111_3
    | exact certificate_sound 15 111 4 cell_15_111_4
    | exact certificate_sound 15 111 5 cell_15_111_5
theorem cell_15_112_0 : CertificateAt 15 112 0 := by decide +kernel
theorem cell_15_112_1 : CertificateAt 15 112 1 := by decide +kernel
theorem cell_15_112_2 : CertificateAt 15 112 2 := by decide +kernel
theorem cell_15_112_3 : CertificateAt 15 112 3 := by decide +kernel
theorem cell_15_112_4 : CertificateAt 15 112 4 := by decide +kernel
theorem cell_15_112_5 : CertificateAt 15 112 5 := by decide +kernel
theorem row_15_112 : ThresholdAt 15 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 112 0 cell_15_112_0
    | exact certificate_sound 15 112 1 cell_15_112_1
    | exact certificate_sound 15 112 2 cell_15_112_2
    | exact certificate_sound 15 112 3 cell_15_112_3
    | exact certificate_sound 15 112 4 cell_15_112_4
    | exact certificate_sound 15 112 5 cell_15_112_5
theorem cell_15_113_0 : CertificateAt 15 113 0 := by decide +kernel
theorem cell_15_113_1 : CertificateAt 15 113 1 := by decide +kernel
theorem cell_15_113_2 : CertificateAt 15 113 2 := by decide +kernel
theorem cell_15_113_3 : CertificateAt 15 113 3 := by decide +kernel
theorem cell_15_113_4 : CertificateAt 15 113 4 := by decide +kernel
theorem cell_15_113_5 : CertificateAt 15 113 5 := by decide +kernel
theorem row_15_113 : ThresholdAt 15 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 113 0 cell_15_113_0
    | exact certificate_sound 15 113 1 cell_15_113_1
    | exact certificate_sound 15 113 2 cell_15_113_2
    | exact certificate_sound 15 113 3 cell_15_113_3
    | exact certificate_sound 15 113 4 cell_15_113_4
    | exact certificate_sound 15 113 5 cell_15_113_5
theorem cell_15_114_0 : CertificateAt 15 114 0 := by decide +kernel
theorem cell_15_114_1 : CertificateAt 15 114 1 := by decide +kernel
theorem cell_15_114_2 : CertificateAt 15 114 2 := by decide +kernel
theorem cell_15_114_3 : CertificateAt 15 114 3 := by decide +kernel
theorem cell_15_114_4 : CertificateAt 15 114 4 := by decide +kernel
theorem cell_15_114_5 : CertificateAt 15 114 5 := by decide +kernel
theorem row_15_114 : ThresholdAt 15 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 114 0 cell_15_114_0
    | exact certificate_sound 15 114 1 cell_15_114_1
    | exact certificate_sound 15 114 2 cell_15_114_2
    | exact certificate_sound 15 114 3 cell_15_114_3
    | exact certificate_sound 15 114 4 cell_15_114_4
    | exact certificate_sound 15 114 5 cell_15_114_5
theorem cell_15_115_0 : CertificateAt 15 115 0 := by decide +kernel
theorem cell_15_115_1 : CertificateAt 15 115 1 := by decide +kernel
theorem cell_15_115_2 : CertificateAt 15 115 2 := by decide +kernel
theorem cell_15_115_3 : CertificateAt 15 115 3 := by decide +kernel
theorem cell_15_115_4 : CertificateAt 15 115 4 := by decide +kernel
theorem cell_15_115_5 : CertificateAt 15 115 5 := by decide +kernel
theorem row_15_115 : ThresholdAt 15 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 115 0 cell_15_115_0
    | exact certificate_sound 15 115 1 cell_15_115_1
    | exact certificate_sound 15 115 2 cell_15_115_2
    | exact certificate_sound 15 115 3 cell_15_115_3
    | exact certificate_sound 15 115 4 cell_15_115_4
    | exact certificate_sound 15 115 5 cell_15_115_5
theorem cell_15_116_0 : CertificateAt 15 116 0 := by decide +kernel
theorem cell_15_116_1 : CertificateAt 15 116 1 := by decide +kernel
theorem cell_15_116_2 : CertificateAt 15 116 2 := by decide +kernel
theorem cell_15_116_3 : CertificateAt 15 116 3 := by decide +kernel
theorem cell_15_116_4 : CertificateAt 15 116 4 := by decide +kernel
theorem cell_15_116_5 : CertificateAt 15 116 5 := by decide +kernel
theorem row_15_116 : ThresholdAt 15 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 116 0 cell_15_116_0
    | exact certificate_sound 15 116 1 cell_15_116_1
    | exact certificate_sound 15 116 2 cell_15_116_2
    | exact certificate_sound 15 116 3 cell_15_116_3
    | exact certificate_sound 15 116 4 cell_15_116_4
    | exact certificate_sound 15 116 5 cell_15_116_5
theorem cell_15_117_0 : CertificateAt 15 117 0 := by decide +kernel
theorem cell_15_117_1 : CertificateAt 15 117 1 := by decide +kernel
theorem cell_15_117_2 : CertificateAt 15 117 2 := by decide +kernel
theorem cell_15_117_3 : CertificateAt 15 117 3 := by decide +kernel
theorem cell_15_117_4 : CertificateAt 15 117 4 := by decide +kernel
theorem cell_15_117_5 : CertificateAt 15 117 5 := by decide +kernel
theorem row_15_117 : ThresholdAt 15 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 117 0 cell_15_117_0
    | exact certificate_sound 15 117 1 cell_15_117_1
    | exact certificate_sound 15 117 2 cell_15_117_2
    | exact certificate_sound 15 117 3 cell_15_117_3
    | exact certificate_sound 15 117 4 cell_15_117_4
    | exact certificate_sound 15 117 5 cell_15_117_5
theorem cell_15_118_0 : CertificateAt 15 118 0 := by decide +kernel
theorem cell_15_118_1 : CertificateAt 15 118 1 := by decide +kernel
theorem cell_15_118_2 : CertificateAt 15 118 2 := by decide +kernel
theorem cell_15_118_3 : CertificateAt 15 118 3 := by decide +kernel
theorem cell_15_118_4 : CertificateAt 15 118 4 := by decide +kernel
theorem cell_15_118_5 : CertificateAt 15 118 5 := by decide +kernel
theorem row_15_118 : ThresholdAt 15 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 118 0 cell_15_118_0
    | exact certificate_sound 15 118 1 cell_15_118_1
    | exact certificate_sound 15 118 2 cell_15_118_2
    | exact certificate_sound 15 118 3 cell_15_118_3
    | exact certificate_sound 15 118 4 cell_15_118_4
    | exact certificate_sound 15 118 5 cell_15_118_5
theorem cell_15_119_0 : CertificateAt 15 119 0 := by decide +kernel
theorem cell_15_119_1 : CertificateAt 15 119 1 := by decide +kernel
theorem cell_15_119_2 : CertificateAt 15 119 2 := by decide +kernel
theorem cell_15_119_3 : CertificateAt 15 119 3 := by decide +kernel
theorem cell_15_119_4 : CertificateAt 15 119 4 := by decide +kernel
theorem cell_15_119_5 : CertificateAt 15 119 5 := by decide +kernel
theorem row_15_119 : ThresholdAt 15 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 119 0 cell_15_119_0
    | exact certificate_sound 15 119 1 cell_15_119_1
    | exact certificate_sound 15 119 2 cell_15_119_2
    | exact certificate_sound 15 119 3 cell_15_119_3
    | exact certificate_sound 15 119 4 cell_15_119_4
    | exact certificate_sound 15 119 5 cell_15_119_5
theorem cell_15_120_0 : CertificateAt 15 120 0 := by decide +kernel
theorem cell_15_120_1 : CertificateAt 15 120 1 := by decide +kernel
theorem cell_15_120_2 : CertificateAt 15 120 2 := by decide +kernel
theorem cell_15_120_3 : CertificateAt 15 120 3 := by decide +kernel
theorem cell_15_120_4 : CertificateAt 15 120 4 := by decide +kernel
theorem cell_15_120_5 : CertificateAt 15 120 5 := by decide +kernel
theorem row_15_120 : ThresholdAt 15 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 120 0 cell_15_120_0
    | exact certificate_sound 15 120 1 cell_15_120_1
    | exact certificate_sound 15 120 2 cell_15_120_2
    | exact certificate_sound 15 120 3 cell_15_120_3
    | exact certificate_sound 15 120 4 cell_15_120_4
    | exact certificate_sound 15 120 5 cell_15_120_5
theorem cell_15_121_0 : CertificateAt 15 121 0 := by decide +kernel
theorem cell_15_121_1 : CertificateAt 15 121 1 := by decide +kernel
theorem cell_15_121_2 : CertificateAt 15 121 2 := by decide +kernel
theorem cell_15_121_3 : CertificateAt 15 121 3 := by decide +kernel
theorem cell_15_121_4 : CertificateAt 15 121 4 := by decide +kernel
theorem cell_15_121_5 : CertificateAt 15 121 5 := by decide +kernel
theorem row_15_121 : ThresholdAt 15 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 121 0 cell_15_121_0
    | exact certificate_sound 15 121 1 cell_15_121_1
    | exact certificate_sound 15 121 2 cell_15_121_2
    | exact certificate_sound 15 121 3 cell_15_121_3
    | exact certificate_sound 15 121 4 cell_15_121_4
    | exact certificate_sound 15 121 5 cell_15_121_5
theorem cell_15_122_0 : CertificateAt 15 122 0 := by decide +kernel
theorem cell_15_122_1 : CertificateAt 15 122 1 := by decide +kernel
theorem cell_15_122_2 : CertificateAt 15 122 2 := by decide +kernel
theorem cell_15_122_3 : CertificateAt 15 122 3 := by decide +kernel
theorem cell_15_122_4 : CertificateAt 15 122 4 := by decide +kernel
theorem cell_15_122_5 : CertificateAt 15 122 5 := by decide +kernel
theorem row_15_122 : ThresholdAt 15 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 122 0 cell_15_122_0
    | exact certificate_sound 15 122 1 cell_15_122_1
    | exact certificate_sound 15 122 2 cell_15_122_2
    | exact certificate_sound 15 122 3 cell_15_122_3
    | exact certificate_sound 15 122 4 cell_15_122_4
    | exact certificate_sound 15 122 5 cell_15_122_5
theorem cell_15_123_0 : CertificateAt 15 123 0 := by decide +kernel
theorem cell_15_123_1 : CertificateAt 15 123 1 := by decide +kernel
theorem cell_15_123_2 : CertificateAt 15 123 2 := by decide +kernel
theorem cell_15_123_3 : CertificateAt 15 123 3 := by decide +kernel
theorem cell_15_123_4 : CertificateAt 15 123 4 := by decide +kernel
theorem cell_15_123_5 : CertificateAt 15 123 5 := by decide +kernel
theorem row_15_123 : ThresholdAt 15 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 123 0 cell_15_123_0
    | exact certificate_sound 15 123 1 cell_15_123_1
    | exact certificate_sound 15 123 2 cell_15_123_2
    | exact certificate_sound 15 123 3 cell_15_123_3
    | exact certificate_sound 15 123 4 cell_15_123_4
    | exact certificate_sound 15 123 5 cell_15_123_5
theorem cell_15_124_0 : CertificateAt 15 124 0 := by decide +kernel
theorem cell_15_124_1 : CertificateAt 15 124 1 := by decide +kernel
theorem cell_15_124_2 : CertificateAt 15 124 2 := by decide +kernel
theorem cell_15_124_3 : CertificateAt 15 124 3 := by decide +kernel
theorem cell_15_124_4 : CertificateAt 15 124 4 := by decide +kernel
theorem cell_15_124_5 : CertificateAt 15 124 5 := by decide +kernel
theorem row_15_124 : ThresholdAt 15 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 15 124 0 cell_15_124_0
    | exact certificate_sound 15 124 1 cell_15_124_1
    | exact certificate_sound 15 124 2 cell_15_124_2
    | exact certificate_sound 15 124 3 cell_15_124_3
    | exact certificate_sound 15 124 4 cell_15_124_4
    | exact certificate_sound 15 124 5 cell_15_124_5
theorem checkedR15 : ∀ V ∈ List.range 125, ThresholdAt 15 V := by
  intro V hV
  have hv : V < 125 := List.mem_range.mp hV
  by_cases h0_125 : V < 62
  · by_cases h0_62 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_15_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_15_1
              · have he : V = 2 := by omega
                subst V
                exact row_15_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_15_3
              · have he : V = 4 := by omega
                subst V
                exact row_15_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_15_5
              · have he : V = 6 := by omega
                subst V
                exact row_15_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_15_7
              · have he : V = 8 := by omega
                subst V
                exact row_15_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_15_9
              · have he : V = 10 := by omega
                subst V
                exact row_15_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_15_11
              · have he : V = 12 := by omega
                subst V
                exact row_15_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_15_13
              · have he : V = 14 := by omega
                subst V
                exact row_15_14
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_15_15
              · have he : V = 16 := by omega
                subst V
                exact row_15_16
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_15_17
              · have he : V = 18 := by omega
                subst V
                exact row_15_18
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_15_19
              · have he : V = 20 := by omega
                subst V
                exact row_15_20
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_15_21
              · have he : V = 22 := by omega
                subst V
                exact row_15_22
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_15_23
              · have he : V = 24 := by omega
                subst V
                exact row_15_24
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_15_25
              · have he : V = 26 := by omega
                subst V
                exact row_15_26
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_15_27
              · have he : V = 28 := by omega
                subst V
                exact row_15_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_15_29
              · have he : V = 30 := by omega
                subst V
                exact row_15_30
    · by_cases h31_62 : V < 46
      · by_cases h31_46 : V < 38
        · by_cases h31_38 : V < 34
          · by_cases h31_34 : V < 32
            · have he : V = 31 := by omega
              subst V
              exact row_15_31
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_15_32
              · have he : V = 33 := by omega
                subst V
                exact row_15_33
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_15_34
              · have he : V = 35 := by omega
                subst V
                exact row_15_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_15_36
              · have he : V = 37 := by omega
                subst V
                exact row_15_37
        · by_cases h38_46 : V < 42
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_15_38
              · have he : V = 39 := by omega
                subst V
                exact row_15_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_15_40
              · have he : V = 41 := by omega
                subst V
                exact row_15_41
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_15_42
              · have he : V = 43 := by omega
                subst V
                exact row_15_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_15_44
              · have he : V = 45 := by omega
                subst V
                exact row_15_45
      · by_cases h46_62 : V < 54
        · by_cases h46_54 : V < 50
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_15_46
              · have he : V = 47 := by omega
                subst V
                exact row_15_47
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_15_48
              · have he : V = 49 := by omega
                subst V
                exact row_15_49
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_15_50
              · have he : V = 51 := by omega
                subst V
                exact row_15_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_15_52
              · have he : V = 53 := by omega
                subst V
                exact row_15_53
        · by_cases h54_62 : V < 58
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_15_54
              · have he : V = 55 := by omega
                subst V
                exact row_15_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_15_56
              · have he : V = 57 := by omega
                subst V
                exact row_15_57
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_15_58
              · have he : V = 59 := by omega
                subst V
                exact row_15_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_15_60
              · have he : V = 61 := by omega
                subst V
                exact row_15_61
  · by_cases h62_125 : V < 93
    · by_cases h62_93 : V < 77
      · by_cases h62_77 : V < 69
        · by_cases h62_69 : V < 65
          · by_cases h62_65 : V < 63
            · have he : V = 62 := by omega
              subst V
              exact row_15_62
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_15_63
              · have he : V = 64 := by omega
                subst V
                exact row_15_64
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_15_65
              · have he : V = 66 := by omega
                subst V
                exact row_15_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_15_67
              · have he : V = 68 := by omega
                subst V
                exact row_15_68
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_15_69
              · have he : V = 70 := by omega
                subst V
                exact row_15_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_15_71
              · have he : V = 72 := by omega
                subst V
                exact row_15_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_15_73
              · have he : V = 74 := by omega
                subst V
                exact row_15_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_15_75
              · have he : V = 76 := by omega
                subst V
                exact row_15_76
      · by_cases h77_93 : V < 85
        · by_cases h77_85 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_15_77
              · have he : V = 78 := by omega
                subst V
                exact row_15_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_15_79
              · have he : V = 80 := by omega
                subst V
                exact row_15_80
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_15_81
              · have he : V = 82 := by omega
                subst V
                exact row_15_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_15_83
              · have he : V = 84 := by omega
                subst V
                exact row_15_84
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_15_85
              · have he : V = 86 := by omega
                subst V
                exact row_15_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_15_87
              · have he : V = 88 := by omega
                subst V
                exact row_15_88
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_15_89
              · have he : V = 90 := by omega
                subst V
                exact row_15_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_15_91
              · have he : V = 92 := by omega
                subst V
                exact row_15_92
    · by_cases h93_125 : V < 109
      · by_cases h93_109 : V < 101
        · by_cases h93_101 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_15_93
              · have he : V = 94 := by omega
                subst V
                exact row_15_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_15_95
              · have he : V = 96 := by omega
                subst V
                exact row_15_96
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_15_97
              · have he : V = 98 := by omega
                subst V
                exact row_15_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_15_99
              · have he : V = 100 := by omega
                subst V
                exact row_15_100
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_15_101
              · have he : V = 102 := by omega
                subst V
                exact row_15_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_15_103
              · have he : V = 104 := by omega
                subst V
                exact row_15_104
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_15_105
              · have he : V = 106 := by omega
                subst V
                exact row_15_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_15_107
              · have he : V = 108 := by omega
                subst V
                exact row_15_108
      · by_cases h109_125 : V < 117
        · by_cases h109_117 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_15_109
              · have he : V = 110 := by omega
                subst V
                exact row_15_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_15_111
              · have he : V = 112 := by omega
                subst V
                exact row_15_112
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_15_113
              · have he : V = 114 := by omega
                subst V
                exact row_15_114
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_15_115
              · have he : V = 116 := by omega
                subst V
                exact row_15_116
        · by_cases h117_125 : V < 121
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_15_117
              · have he : V = 118 := by omega
                subst V
                exact row_15_118
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_15_119
              · have he : V = 120 := by omega
                subst V
                exact row_15_120
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_15_121
              · have he : V = 122 := by omega
                subst V
                exact row_15_122
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_15_123
              · have he : V = 124 := by omega
                subst V
                exact row_15_124
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
