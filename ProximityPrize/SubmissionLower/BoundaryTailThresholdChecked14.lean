import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked13

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_14_0_0 : CertificateAt 14 0 0 := by decide +kernel
theorem cell_14_0_1 : CertificateAt 14 0 1 := by decide +kernel
theorem cell_14_0_2 : CertificateAt 14 0 2 := by decide +kernel
theorem cell_14_0_3 : CertificateAt 14 0 3 := by decide +kernel
theorem cell_14_0_4 : CertificateAt 14 0 4 := by decide +kernel
theorem cell_14_0_5 : CertificateAt 14 0 5 := by decide +kernel
theorem row_14_0 : ThresholdAt 14 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 0 0 cell_14_0_0
    | exact certificate_sound 14 0 1 cell_14_0_1
    | exact certificate_sound 14 0 2 cell_14_0_2
    | exact certificate_sound 14 0 3 cell_14_0_3
    | exact certificate_sound 14 0 4 cell_14_0_4
    | exact certificate_sound 14 0 5 cell_14_0_5
theorem cell_14_1_0 : CertificateAt 14 1 0 := by decide +kernel
theorem cell_14_1_1 : CertificateAt 14 1 1 := by decide +kernel
theorem cell_14_1_2 : CertificateAt 14 1 2 := by decide +kernel
theorem cell_14_1_3 : CertificateAt 14 1 3 := by decide +kernel
theorem cell_14_1_4 : CertificateAt 14 1 4 := by decide +kernel
theorem cell_14_1_5 : CertificateAt 14 1 5 := by decide +kernel
theorem row_14_1 : ThresholdAt 14 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 1 0 cell_14_1_0
    | exact certificate_sound 14 1 1 cell_14_1_1
    | exact certificate_sound 14 1 2 cell_14_1_2
    | exact certificate_sound 14 1 3 cell_14_1_3
    | exact certificate_sound 14 1 4 cell_14_1_4
    | exact certificate_sound 14 1 5 cell_14_1_5
theorem cell_14_2_0 : CertificateAt 14 2 0 := by decide +kernel
theorem cell_14_2_1 : CertificateAt 14 2 1 := by decide +kernel
theorem cell_14_2_2 : CertificateAt 14 2 2 := by decide +kernel
theorem cell_14_2_3 : CertificateAt 14 2 3 := by decide +kernel
theorem cell_14_2_4 : CertificateAt 14 2 4 := by decide +kernel
theorem cell_14_2_5 : CertificateAt 14 2 5 := by decide +kernel
theorem row_14_2 : ThresholdAt 14 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 2 0 cell_14_2_0
    | exact certificate_sound 14 2 1 cell_14_2_1
    | exact certificate_sound 14 2 2 cell_14_2_2
    | exact certificate_sound 14 2 3 cell_14_2_3
    | exact certificate_sound 14 2 4 cell_14_2_4
    | exact certificate_sound 14 2 5 cell_14_2_5
theorem cell_14_3_0 : CertificateAt 14 3 0 := by decide +kernel
theorem cell_14_3_1 : CertificateAt 14 3 1 := by decide +kernel
theorem cell_14_3_2 : CertificateAt 14 3 2 := by decide +kernel
theorem cell_14_3_3 : CertificateAt 14 3 3 := by decide +kernel
theorem cell_14_3_4 : CertificateAt 14 3 4 := by decide +kernel
theorem cell_14_3_5 : CertificateAt 14 3 5 := by decide +kernel
theorem row_14_3 : ThresholdAt 14 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 3 0 cell_14_3_0
    | exact certificate_sound 14 3 1 cell_14_3_1
    | exact certificate_sound 14 3 2 cell_14_3_2
    | exact certificate_sound 14 3 3 cell_14_3_3
    | exact certificate_sound 14 3 4 cell_14_3_4
    | exact certificate_sound 14 3 5 cell_14_3_5
theorem cell_14_4_0 : CertificateAt 14 4 0 := by decide +kernel
theorem cell_14_4_1 : CertificateAt 14 4 1 := by decide +kernel
theorem cell_14_4_2 : CertificateAt 14 4 2 := by decide +kernel
theorem cell_14_4_3 : CertificateAt 14 4 3 := by decide +kernel
theorem cell_14_4_4 : CertificateAt 14 4 4 := by decide +kernel
theorem cell_14_4_5 : CertificateAt 14 4 5 := by decide +kernel
theorem row_14_4 : ThresholdAt 14 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 4 0 cell_14_4_0
    | exact certificate_sound 14 4 1 cell_14_4_1
    | exact certificate_sound 14 4 2 cell_14_4_2
    | exact certificate_sound 14 4 3 cell_14_4_3
    | exact certificate_sound 14 4 4 cell_14_4_4
    | exact certificate_sound 14 4 5 cell_14_4_5
theorem cell_14_5_0 : CertificateAt 14 5 0 := by decide +kernel
theorem cell_14_5_1 : CertificateAt 14 5 1 := by decide +kernel
theorem cell_14_5_2 : CertificateAt 14 5 2 := by decide +kernel
theorem cell_14_5_3 : CertificateAt 14 5 3 := by decide +kernel
theorem cell_14_5_4 : CertificateAt 14 5 4 := by decide +kernel
theorem cell_14_5_5 : CertificateAt 14 5 5 := by decide +kernel
theorem row_14_5 : ThresholdAt 14 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 5 0 cell_14_5_0
    | exact certificate_sound 14 5 1 cell_14_5_1
    | exact certificate_sound 14 5 2 cell_14_5_2
    | exact certificate_sound 14 5 3 cell_14_5_3
    | exact certificate_sound 14 5 4 cell_14_5_4
    | exact certificate_sound 14 5 5 cell_14_5_5
theorem cell_14_6_0 : CertificateAt 14 6 0 := by decide +kernel
theorem cell_14_6_1 : CertificateAt 14 6 1 := by decide +kernel
theorem cell_14_6_2 : CertificateAt 14 6 2 := by decide +kernel
theorem cell_14_6_3 : CertificateAt 14 6 3 := by decide +kernel
theorem cell_14_6_4 : CertificateAt 14 6 4 := by decide +kernel
theorem cell_14_6_5 : CertificateAt 14 6 5 := by decide +kernel
theorem row_14_6 : ThresholdAt 14 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 6 0 cell_14_6_0
    | exact certificate_sound 14 6 1 cell_14_6_1
    | exact certificate_sound 14 6 2 cell_14_6_2
    | exact certificate_sound 14 6 3 cell_14_6_3
    | exact certificate_sound 14 6 4 cell_14_6_4
    | exact certificate_sound 14 6 5 cell_14_6_5
theorem cell_14_7_0 : CertificateAt 14 7 0 := by decide +kernel
theorem cell_14_7_1 : CertificateAt 14 7 1 := by decide +kernel
theorem cell_14_7_2 : CertificateAt 14 7 2 := by decide +kernel
theorem cell_14_7_3 : CertificateAt 14 7 3 := by decide +kernel
theorem cell_14_7_4 : CertificateAt 14 7 4 := by decide +kernel
theorem cell_14_7_5 : CertificateAt 14 7 5 := by decide +kernel
theorem row_14_7 : ThresholdAt 14 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 7 0 cell_14_7_0
    | exact certificate_sound 14 7 1 cell_14_7_1
    | exact certificate_sound 14 7 2 cell_14_7_2
    | exact certificate_sound 14 7 3 cell_14_7_3
    | exact certificate_sound 14 7 4 cell_14_7_4
    | exact certificate_sound 14 7 5 cell_14_7_5
theorem cell_14_8_0 : CertificateAt 14 8 0 := by decide +kernel
theorem cell_14_8_1 : CertificateAt 14 8 1 := by decide +kernel
theorem cell_14_8_2 : CertificateAt 14 8 2 := by decide +kernel
theorem cell_14_8_3 : CertificateAt 14 8 3 := by decide +kernel
theorem cell_14_8_4 : CertificateAt 14 8 4 := by decide +kernel
theorem cell_14_8_5 : CertificateAt 14 8 5 := by decide +kernel
theorem row_14_8 : ThresholdAt 14 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 8 0 cell_14_8_0
    | exact certificate_sound 14 8 1 cell_14_8_1
    | exact certificate_sound 14 8 2 cell_14_8_2
    | exact certificate_sound 14 8 3 cell_14_8_3
    | exact certificate_sound 14 8 4 cell_14_8_4
    | exact certificate_sound 14 8 5 cell_14_8_5
theorem cell_14_9_0 : CertificateAt 14 9 0 := by decide +kernel
theorem cell_14_9_1 : CertificateAt 14 9 1 := by decide +kernel
theorem cell_14_9_2 : CertificateAt 14 9 2 := by decide +kernel
theorem cell_14_9_3 : CertificateAt 14 9 3 := by decide +kernel
theorem cell_14_9_4 : CertificateAt 14 9 4 := by decide +kernel
theorem cell_14_9_5 : CertificateAt 14 9 5 := by decide +kernel
theorem row_14_9 : ThresholdAt 14 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 9 0 cell_14_9_0
    | exact certificate_sound 14 9 1 cell_14_9_1
    | exact certificate_sound 14 9 2 cell_14_9_2
    | exact certificate_sound 14 9 3 cell_14_9_3
    | exact certificate_sound 14 9 4 cell_14_9_4
    | exact certificate_sound 14 9 5 cell_14_9_5
theorem cell_14_10_0 : CertificateAt 14 10 0 := by decide +kernel
theorem cell_14_10_1 : CertificateAt 14 10 1 := by decide +kernel
theorem cell_14_10_2 : CertificateAt 14 10 2 := by decide +kernel
theorem cell_14_10_3 : CertificateAt 14 10 3 := by decide +kernel
theorem cell_14_10_4 : CertificateAt 14 10 4 := by decide +kernel
theorem cell_14_10_5 : CertificateAt 14 10 5 := by decide +kernel
theorem row_14_10 : ThresholdAt 14 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 10 0 cell_14_10_0
    | exact certificate_sound 14 10 1 cell_14_10_1
    | exact certificate_sound 14 10 2 cell_14_10_2
    | exact certificate_sound 14 10 3 cell_14_10_3
    | exact certificate_sound 14 10 4 cell_14_10_4
    | exact certificate_sound 14 10 5 cell_14_10_5
theorem cell_14_11_0 : CertificateAt 14 11 0 := by decide +kernel
theorem cell_14_11_1 : CertificateAt 14 11 1 := by decide +kernel
theorem cell_14_11_2 : CertificateAt 14 11 2 := by decide +kernel
theorem cell_14_11_3 : CertificateAt 14 11 3 := by decide +kernel
theorem cell_14_11_4 : CertificateAt 14 11 4 := by decide +kernel
theorem cell_14_11_5 : CertificateAt 14 11 5 := by decide +kernel
theorem row_14_11 : ThresholdAt 14 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 11 0 cell_14_11_0
    | exact certificate_sound 14 11 1 cell_14_11_1
    | exact certificate_sound 14 11 2 cell_14_11_2
    | exact certificate_sound 14 11 3 cell_14_11_3
    | exact certificate_sound 14 11 4 cell_14_11_4
    | exact certificate_sound 14 11 5 cell_14_11_5
theorem cell_14_12_0 : CertificateAt 14 12 0 := by decide +kernel
theorem cell_14_12_1 : CertificateAt 14 12 1 := by decide +kernel
theorem cell_14_12_2 : CertificateAt 14 12 2 := by decide +kernel
theorem cell_14_12_3 : CertificateAt 14 12 3 := by decide +kernel
theorem cell_14_12_4 : CertificateAt 14 12 4 := by decide +kernel
theorem cell_14_12_5 : CertificateAt 14 12 5 := by decide +kernel
theorem row_14_12 : ThresholdAt 14 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 12 0 cell_14_12_0
    | exact certificate_sound 14 12 1 cell_14_12_1
    | exact certificate_sound 14 12 2 cell_14_12_2
    | exact certificate_sound 14 12 3 cell_14_12_3
    | exact certificate_sound 14 12 4 cell_14_12_4
    | exact certificate_sound 14 12 5 cell_14_12_5
theorem cell_14_13_0 : CertificateAt 14 13 0 := by decide +kernel
theorem cell_14_13_1 : CertificateAt 14 13 1 := by decide +kernel
theorem cell_14_13_2 : CertificateAt 14 13 2 := by decide +kernel
theorem cell_14_13_3 : CertificateAt 14 13 3 := by decide +kernel
theorem cell_14_13_4 : CertificateAt 14 13 4 := by decide +kernel
theorem cell_14_13_5 : CertificateAt 14 13 5 := by decide +kernel
theorem row_14_13 : ThresholdAt 14 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 13 0 cell_14_13_0
    | exact certificate_sound 14 13 1 cell_14_13_1
    | exact certificate_sound 14 13 2 cell_14_13_2
    | exact certificate_sound 14 13 3 cell_14_13_3
    | exact certificate_sound 14 13 4 cell_14_13_4
    | exact certificate_sound 14 13 5 cell_14_13_5
theorem cell_14_14_0 : CertificateAt 14 14 0 := by decide +kernel
theorem cell_14_14_1 : CertificateAt 14 14 1 := by decide +kernel
theorem cell_14_14_2 : CertificateAt 14 14 2 := by decide +kernel
theorem cell_14_14_3 : CertificateAt 14 14 3 := by decide +kernel
theorem cell_14_14_4 : CertificateAt 14 14 4 := by decide +kernel
theorem cell_14_14_5 : CertificateAt 14 14 5 := by decide +kernel
theorem row_14_14 : ThresholdAt 14 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 14 0 cell_14_14_0
    | exact certificate_sound 14 14 1 cell_14_14_1
    | exact certificate_sound 14 14 2 cell_14_14_2
    | exact certificate_sound 14 14 3 cell_14_14_3
    | exact certificate_sound 14 14 4 cell_14_14_4
    | exact certificate_sound 14 14 5 cell_14_14_5
theorem cell_14_15_0 : CertificateAt 14 15 0 := by decide +kernel
theorem cell_14_15_1 : CertificateAt 14 15 1 := by decide +kernel
theorem cell_14_15_2 : CertificateAt 14 15 2 := by decide +kernel
theorem cell_14_15_3 : CertificateAt 14 15 3 := by decide +kernel
theorem cell_14_15_4 : CertificateAt 14 15 4 := by decide +kernel
theorem cell_14_15_5 : CertificateAt 14 15 5 := by decide +kernel
theorem row_14_15 : ThresholdAt 14 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 15 0 cell_14_15_0
    | exact certificate_sound 14 15 1 cell_14_15_1
    | exact certificate_sound 14 15 2 cell_14_15_2
    | exact certificate_sound 14 15 3 cell_14_15_3
    | exact certificate_sound 14 15 4 cell_14_15_4
    | exact certificate_sound 14 15 5 cell_14_15_5
theorem cell_14_16_0 : CertificateAt 14 16 0 := by decide +kernel
theorem cell_14_16_1 : CertificateAt 14 16 1 := by decide +kernel
theorem cell_14_16_2 : CertificateAt 14 16 2 := by decide +kernel
theorem cell_14_16_3 : CertificateAt 14 16 3 := by decide +kernel
theorem cell_14_16_4 : CertificateAt 14 16 4 := by decide +kernel
theorem cell_14_16_5 : CertificateAt 14 16 5 := by decide +kernel
theorem row_14_16 : ThresholdAt 14 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 16 0 cell_14_16_0
    | exact certificate_sound 14 16 1 cell_14_16_1
    | exact certificate_sound 14 16 2 cell_14_16_2
    | exact certificate_sound 14 16 3 cell_14_16_3
    | exact certificate_sound 14 16 4 cell_14_16_4
    | exact certificate_sound 14 16 5 cell_14_16_5
theorem cell_14_17_0 : CertificateAt 14 17 0 := by decide +kernel
theorem cell_14_17_1 : CertificateAt 14 17 1 := by decide +kernel
theorem cell_14_17_2 : CertificateAt 14 17 2 := by decide +kernel
theorem cell_14_17_3 : CertificateAt 14 17 3 := by decide +kernel
theorem cell_14_17_4 : CertificateAt 14 17 4 := by decide +kernel
theorem cell_14_17_5 : CertificateAt 14 17 5 := by decide +kernel
theorem row_14_17 : ThresholdAt 14 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 17 0 cell_14_17_0
    | exact certificate_sound 14 17 1 cell_14_17_1
    | exact certificate_sound 14 17 2 cell_14_17_2
    | exact certificate_sound 14 17 3 cell_14_17_3
    | exact certificate_sound 14 17 4 cell_14_17_4
    | exact certificate_sound 14 17 5 cell_14_17_5
theorem cell_14_18_0 : CertificateAt 14 18 0 := by decide +kernel
theorem cell_14_18_1 : CertificateAt 14 18 1 := by decide +kernel
theorem cell_14_18_2 : CertificateAt 14 18 2 := by decide +kernel
theorem cell_14_18_3 : CertificateAt 14 18 3 := by decide +kernel
theorem cell_14_18_4 : CertificateAt 14 18 4 := by decide +kernel
theorem cell_14_18_5 : CertificateAt 14 18 5 := by decide +kernel
theorem row_14_18 : ThresholdAt 14 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 18 0 cell_14_18_0
    | exact certificate_sound 14 18 1 cell_14_18_1
    | exact certificate_sound 14 18 2 cell_14_18_2
    | exact certificate_sound 14 18 3 cell_14_18_3
    | exact certificate_sound 14 18 4 cell_14_18_4
    | exact certificate_sound 14 18 5 cell_14_18_5
theorem cell_14_19_0 : CertificateAt 14 19 0 := by decide +kernel
theorem cell_14_19_1 : CertificateAt 14 19 1 := by decide +kernel
theorem cell_14_19_2 : CertificateAt 14 19 2 := by decide +kernel
theorem cell_14_19_3 : CertificateAt 14 19 3 := by decide +kernel
theorem cell_14_19_4 : CertificateAt 14 19 4 := by decide +kernel
theorem cell_14_19_5 : CertificateAt 14 19 5 := by decide +kernel
theorem row_14_19 : ThresholdAt 14 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 19 0 cell_14_19_0
    | exact certificate_sound 14 19 1 cell_14_19_1
    | exact certificate_sound 14 19 2 cell_14_19_2
    | exact certificate_sound 14 19 3 cell_14_19_3
    | exact certificate_sound 14 19 4 cell_14_19_4
    | exact certificate_sound 14 19 5 cell_14_19_5
theorem cell_14_20_0 : CertificateAt 14 20 0 := by decide +kernel
theorem cell_14_20_1 : CertificateAt 14 20 1 := by decide +kernel
theorem cell_14_20_2 : CertificateAt 14 20 2 := by decide +kernel
theorem cell_14_20_3 : CertificateAt 14 20 3 := by decide +kernel
theorem cell_14_20_4 : CertificateAt 14 20 4 := by decide +kernel
theorem cell_14_20_5 : CertificateAt 14 20 5 := by decide +kernel
theorem row_14_20 : ThresholdAt 14 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 20 0 cell_14_20_0
    | exact certificate_sound 14 20 1 cell_14_20_1
    | exact certificate_sound 14 20 2 cell_14_20_2
    | exact certificate_sound 14 20 3 cell_14_20_3
    | exact certificate_sound 14 20 4 cell_14_20_4
    | exact certificate_sound 14 20 5 cell_14_20_5
theorem cell_14_21_0 : CertificateAt 14 21 0 := by decide +kernel
theorem cell_14_21_1 : CertificateAt 14 21 1 := by decide +kernel
theorem cell_14_21_2 : CertificateAt 14 21 2 := by decide +kernel
theorem cell_14_21_3 : CertificateAt 14 21 3 := by decide +kernel
theorem cell_14_21_4 : CertificateAt 14 21 4 := by decide +kernel
theorem cell_14_21_5 : CertificateAt 14 21 5 := by decide +kernel
theorem row_14_21 : ThresholdAt 14 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 21 0 cell_14_21_0
    | exact certificate_sound 14 21 1 cell_14_21_1
    | exact certificate_sound 14 21 2 cell_14_21_2
    | exact certificate_sound 14 21 3 cell_14_21_3
    | exact certificate_sound 14 21 4 cell_14_21_4
    | exact certificate_sound 14 21 5 cell_14_21_5
theorem cell_14_22_0 : CertificateAt 14 22 0 := by decide +kernel
theorem cell_14_22_1 : CertificateAt 14 22 1 := by decide +kernel
theorem cell_14_22_2 : CertificateAt 14 22 2 := by decide +kernel
theorem cell_14_22_3 : CertificateAt 14 22 3 := by decide +kernel
theorem cell_14_22_4 : CertificateAt 14 22 4 := by decide +kernel
theorem cell_14_22_5 : CertificateAt 14 22 5 := by decide +kernel
theorem row_14_22 : ThresholdAt 14 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 22 0 cell_14_22_0
    | exact certificate_sound 14 22 1 cell_14_22_1
    | exact certificate_sound 14 22 2 cell_14_22_2
    | exact certificate_sound 14 22 3 cell_14_22_3
    | exact certificate_sound 14 22 4 cell_14_22_4
    | exact certificate_sound 14 22 5 cell_14_22_5
theorem cell_14_23_0 : CertificateAt 14 23 0 := by decide +kernel
theorem cell_14_23_1 : CertificateAt 14 23 1 := by decide +kernel
theorem cell_14_23_2 : CertificateAt 14 23 2 := by decide +kernel
theorem cell_14_23_3 : CertificateAt 14 23 3 := by decide +kernel
theorem cell_14_23_4 : CertificateAt 14 23 4 := by decide +kernel
theorem cell_14_23_5 : CertificateAt 14 23 5 := by decide +kernel
theorem row_14_23 : ThresholdAt 14 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 23 0 cell_14_23_0
    | exact certificate_sound 14 23 1 cell_14_23_1
    | exact certificate_sound 14 23 2 cell_14_23_2
    | exact certificate_sound 14 23 3 cell_14_23_3
    | exact certificate_sound 14 23 4 cell_14_23_4
    | exact certificate_sound 14 23 5 cell_14_23_5
theorem cell_14_24_0 : CertificateAt 14 24 0 := by decide +kernel
theorem cell_14_24_1 : CertificateAt 14 24 1 := by decide +kernel
theorem cell_14_24_2 : CertificateAt 14 24 2 := by decide +kernel
theorem cell_14_24_3 : CertificateAt 14 24 3 := by decide +kernel
theorem cell_14_24_4 : CertificateAt 14 24 4 := by decide +kernel
theorem cell_14_24_5 : CertificateAt 14 24 5 := by decide +kernel
theorem row_14_24 : ThresholdAt 14 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 24 0 cell_14_24_0
    | exact certificate_sound 14 24 1 cell_14_24_1
    | exact certificate_sound 14 24 2 cell_14_24_2
    | exact certificate_sound 14 24 3 cell_14_24_3
    | exact certificate_sound 14 24 4 cell_14_24_4
    | exact certificate_sound 14 24 5 cell_14_24_5
theorem cell_14_25_0 : CertificateAt 14 25 0 := by decide +kernel
theorem cell_14_25_1 : CertificateAt 14 25 1 := by decide +kernel
theorem cell_14_25_2 : CertificateAt 14 25 2 := by decide +kernel
theorem cell_14_25_3 : CertificateAt 14 25 3 := by decide +kernel
theorem cell_14_25_4 : CertificateAt 14 25 4 := by decide +kernel
theorem cell_14_25_5 : CertificateAt 14 25 5 := by decide +kernel
theorem row_14_25 : ThresholdAt 14 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 25 0 cell_14_25_0
    | exact certificate_sound 14 25 1 cell_14_25_1
    | exact certificate_sound 14 25 2 cell_14_25_2
    | exact certificate_sound 14 25 3 cell_14_25_3
    | exact certificate_sound 14 25 4 cell_14_25_4
    | exact certificate_sound 14 25 5 cell_14_25_5
theorem cell_14_26_0 : CertificateAt 14 26 0 := by decide +kernel
theorem cell_14_26_1 : CertificateAt 14 26 1 := by decide +kernel
theorem cell_14_26_2 : CertificateAt 14 26 2 := by decide +kernel
theorem cell_14_26_3 : CertificateAt 14 26 3 := by decide +kernel
theorem cell_14_26_4 : CertificateAt 14 26 4 := by decide +kernel
theorem cell_14_26_5 : CertificateAt 14 26 5 := by decide +kernel
theorem row_14_26 : ThresholdAt 14 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 26 0 cell_14_26_0
    | exact certificate_sound 14 26 1 cell_14_26_1
    | exact certificate_sound 14 26 2 cell_14_26_2
    | exact certificate_sound 14 26 3 cell_14_26_3
    | exact certificate_sound 14 26 4 cell_14_26_4
    | exact certificate_sound 14 26 5 cell_14_26_5
theorem cell_14_27_0 : CertificateAt 14 27 0 := by decide +kernel
theorem cell_14_27_1 : CertificateAt 14 27 1 := by decide +kernel
theorem cell_14_27_2 : CertificateAt 14 27 2 := by decide +kernel
theorem cell_14_27_3 : CertificateAt 14 27 3 := by decide +kernel
theorem cell_14_27_4 : CertificateAt 14 27 4 := by decide +kernel
theorem cell_14_27_5 : CertificateAt 14 27 5 := by decide +kernel
theorem row_14_27 : ThresholdAt 14 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 27 0 cell_14_27_0
    | exact certificate_sound 14 27 1 cell_14_27_1
    | exact certificate_sound 14 27 2 cell_14_27_2
    | exact certificate_sound 14 27 3 cell_14_27_3
    | exact certificate_sound 14 27 4 cell_14_27_4
    | exact certificate_sound 14 27 5 cell_14_27_5
theorem cell_14_28_0 : CertificateAt 14 28 0 := by decide +kernel
theorem cell_14_28_1 : CertificateAt 14 28 1 := by decide +kernel
theorem cell_14_28_2 : CertificateAt 14 28 2 := by decide +kernel
theorem cell_14_28_3 : CertificateAt 14 28 3 := by decide +kernel
theorem cell_14_28_4 : CertificateAt 14 28 4 := by decide +kernel
theorem cell_14_28_5 : CertificateAt 14 28 5 := by decide +kernel
theorem row_14_28 : ThresholdAt 14 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 28 0 cell_14_28_0
    | exact certificate_sound 14 28 1 cell_14_28_1
    | exact certificate_sound 14 28 2 cell_14_28_2
    | exact certificate_sound 14 28 3 cell_14_28_3
    | exact certificate_sound 14 28 4 cell_14_28_4
    | exact certificate_sound 14 28 5 cell_14_28_5
theorem cell_14_29_0 : CertificateAt 14 29 0 := by decide +kernel
theorem cell_14_29_1 : CertificateAt 14 29 1 := by decide +kernel
theorem cell_14_29_2 : CertificateAt 14 29 2 := by decide +kernel
theorem cell_14_29_3 : CertificateAt 14 29 3 := by decide +kernel
theorem cell_14_29_4 : CertificateAt 14 29 4 := by decide +kernel
theorem cell_14_29_5 : CertificateAt 14 29 5 := by decide +kernel
theorem row_14_29 : ThresholdAt 14 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 29 0 cell_14_29_0
    | exact certificate_sound 14 29 1 cell_14_29_1
    | exact certificate_sound 14 29 2 cell_14_29_2
    | exact certificate_sound 14 29 3 cell_14_29_3
    | exact certificate_sound 14 29 4 cell_14_29_4
    | exact certificate_sound 14 29 5 cell_14_29_5
theorem cell_14_30_0 : CertificateAt 14 30 0 := by decide +kernel
theorem cell_14_30_1 : CertificateAt 14 30 1 := by decide +kernel
theorem cell_14_30_2 : CertificateAt 14 30 2 := by decide +kernel
theorem cell_14_30_3 : CertificateAt 14 30 3 := by decide +kernel
theorem cell_14_30_4 : CertificateAt 14 30 4 := by decide +kernel
theorem cell_14_30_5 : CertificateAt 14 30 5 := by decide +kernel
theorem row_14_30 : ThresholdAt 14 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 30 0 cell_14_30_0
    | exact certificate_sound 14 30 1 cell_14_30_1
    | exact certificate_sound 14 30 2 cell_14_30_2
    | exact certificate_sound 14 30 3 cell_14_30_3
    | exact certificate_sound 14 30 4 cell_14_30_4
    | exact certificate_sound 14 30 5 cell_14_30_5
theorem cell_14_31_0 : CertificateAt 14 31 0 := by decide +kernel
theorem cell_14_31_1 : CertificateAt 14 31 1 := by decide +kernel
theorem cell_14_31_2 : CertificateAt 14 31 2 := by decide +kernel
theorem cell_14_31_3 : CertificateAt 14 31 3 := by decide +kernel
theorem cell_14_31_4 : CertificateAt 14 31 4 := by decide +kernel
theorem cell_14_31_5 : CertificateAt 14 31 5 := by decide +kernel
theorem row_14_31 : ThresholdAt 14 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 31 0 cell_14_31_0
    | exact certificate_sound 14 31 1 cell_14_31_1
    | exact certificate_sound 14 31 2 cell_14_31_2
    | exact certificate_sound 14 31 3 cell_14_31_3
    | exact certificate_sound 14 31 4 cell_14_31_4
    | exact certificate_sound 14 31 5 cell_14_31_5
theorem cell_14_32_0 : CertificateAt 14 32 0 := by decide +kernel
theorem cell_14_32_1 : CertificateAt 14 32 1 := by decide +kernel
theorem cell_14_32_2 : CertificateAt 14 32 2 := by decide +kernel
theorem cell_14_32_3 : CertificateAt 14 32 3 := by decide +kernel
theorem cell_14_32_4 : CertificateAt 14 32 4 := by decide +kernel
theorem cell_14_32_5 : CertificateAt 14 32 5 := by decide +kernel
theorem row_14_32 : ThresholdAt 14 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 32 0 cell_14_32_0
    | exact certificate_sound 14 32 1 cell_14_32_1
    | exact certificate_sound 14 32 2 cell_14_32_2
    | exact certificate_sound 14 32 3 cell_14_32_3
    | exact certificate_sound 14 32 4 cell_14_32_4
    | exact certificate_sound 14 32 5 cell_14_32_5
theorem cell_14_33_0 : CertificateAt 14 33 0 := by decide +kernel
theorem cell_14_33_1 : CertificateAt 14 33 1 := by decide +kernel
theorem cell_14_33_2 : CertificateAt 14 33 2 := by decide +kernel
theorem cell_14_33_3 : CertificateAt 14 33 3 := by decide +kernel
theorem cell_14_33_4 : CertificateAt 14 33 4 := by decide +kernel
theorem cell_14_33_5 : CertificateAt 14 33 5 := by decide +kernel
theorem row_14_33 : ThresholdAt 14 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 33 0 cell_14_33_0
    | exact certificate_sound 14 33 1 cell_14_33_1
    | exact certificate_sound 14 33 2 cell_14_33_2
    | exact certificate_sound 14 33 3 cell_14_33_3
    | exact certificate_sound 14 33 4 cell_14_33_4
    | exact certificate_sound 14 33 5 cell_14_33_5
theorem cell_14_34_0 : CertificateAt 14 34 0 := by decide +kernel
theorem cell_14_34_1 : CertificateAt 14 34 1 := by decide +kernel
theorem cell_14_34_2 : CertificateAt 14 34 2 := by decide +kernel
theorem cell_14_34_3 : CertificateAt 14 34 3 := by decide +kernel
theorem cell_14_34_4 : CertificateAt 14 34 4 := by decide +kernel
theorem cell_14_34_5 : CertificateAt 14 34 5 := by decide +kernel
theorem row_14_34 : ThresholdAt 14 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 34 0 cell_14_34_0
    | exact certificate_sound 14 34 1 cell_14_34_1
    | exact certificate_sound 14 34 2 cell_14_34_2
    | exact certificate_sound 14 34 3 cell_14_34_3
    | exact certificate_sound 14 34 4 cell_14_34_4
    | exact certificate_sound 14 34 5 cell_14_34_5
theorem cell_14_35_0 : CertificateAt 14 35 0 := by decide +kernel
theorem cell_14_35_1 : CertificateAt 14 35 1 := by decide +kernel
theorem cell_14_35_2 : CertificateAt 14 35 2 := by decide +kernel
theorem cell_14_35_3 : CertificateAt 14 35 3 := by decide +kernel
theorem cell_14_35_4 : CertificateAt 14 35 4 := by decide +kernel
theorem cell_14_35_5 : CertificateAt 14 35 5 := by decide +kernel
theorem row_14_35 : ThresholdAt 14 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 35 0 cell_14_35_0
    | exact certificate_sound 14 35 1 cell_14_35_1
    | exact certificate_sound 14 35 2 cell_14_35_2
    | exact certificate_sound 14 35 3 cell_14_35_3
    | exact certificate_sound 14 35 4 cell_14_35_4
    | exact certificate_sound 14 35 5 cell_14_35_5
theorem cell_14_36_0 : CertificateAt 14 36 0 := by decide +kernel
theorem cell_14_36_1 : CertificateAt 14 36 1 := by decide +kernel
theorem cell_14_36_2 : CertificateAt 14 36 2 := by decide +kernel
theorem cell_14_36_3 : CertificateAt 14 36 3 := by decide +kernel
theorem cell_14_36_4 : CertificateAt 14 36 4 := by decide +kernel
theorem cell_14_36_5 : CertificateAt 14 36 5 := by decide +kernel
theorem row_14_36 : ThresholdAt 14 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 36 0 cell_14_36_0
    | exact certificate_sound 14 36 1 cell_14_36_1
    | exact certificate_sound 14 36 2 cell_14_36_2
    | exact certificate_sound 14 36 3 cell_14_36_3
    | exact certificate_sound 14 36 4 cell_14_36_4
    | exact certificate_sound 14 36 5 cell_14_36_5
theorem cell_14_37_0 : CertificateAt 14 37 0 := by decide +kernel
theorem cell_14_37_1 : CertificateAt 14 37 1 := by decide +kernel
theorem cell_14_37_2 : CertificateAt 14 37 2 := by decide +kernel
theorem cell_14_37_3 : CertificateAt 14 37 3 := by decide +kernel
theorem cell_14_37_4 : CertificateAt 14 37 4 := by decide +kernel
theorem cell_14_37_5 : CertificateAt 14 37 5 := by decide +kernel
theorem row_14_37 : ThresholdAt 14 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 37 0 cell_14_37_0
    | exact certificate_sound 14 37 1 cell_14_37_1
    | exact certificate_sound 14 37 2 cell_14_37_2
    | exact certificate_sound 14 37 3 cell_14_37_3
    | exact certificate_sound 14 37 4 cell_14_37_4
    | exact certificate_sound 14 37 5 cell_14_37_5
theorem cell_14_38_0 : CertificateAt 14 38 0 := by decide +kernel
theorem cell_14_38_1 : CertificateAt 14 38 1 := by decide +kernel
theorem cell_14_38_2 : CertificateAt 14 38 2 := by decide +kernel
theorem cell_14_38_3 : CertificateAt 14 38 3 := by decide +kernel
theorem cell_14_38_4 : CertificateAt 14 38 4 := by decide +kernel
theorem cell_14_38_5 : CertificateAt 14 38 5 := by decide +kernel
theorem row_14_38 : ThresholdAt 14 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 38 0 cell_14_38_0
    | exact certificate_sound 14 38 1 cell_14_38_1
    | exact certificate_sound 14 38 2 cell_14_38_2
    | exact certificate_sound 14 38 3 cell_14_38_3
    | exact certificate_sound 14 38 4 cell_14_38_4
    | exact certificate_sound 14 38 5 cell_14_38_5
theorem cell_14_39_0 : CertificateAt 14 39 0 := by decide +kernel
theorem cell_14_39_1 : CertificateAt 14 39 1 := by decide +kernel
theorem cell_14_39_2 : CertificateAt 14 39 2 := by decide +kernel
theorem cell_14_39_3 : CertificateAt 14 39 3 := by decide +kernel
theorem cell_14_39_4 : CertificateAt 14 39 4 := by decide +kernel
theorem cell_14_39_5 : CertificateAt 14 39 5 := by decide +kernel
theorem row_14_39 : ThresholdAt 14 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 39 0 cell_14_39_0
    | exact certificate_sound 14 39 1 cell_14_39_1
    | exact certificate_sound 14 39 2 cell_14_39_2
    | exact certificate_sound 14 39 3 cell_14_39_3
    | exact certificate_sound 14 39 4 cell_14_39_4
    | exact certificate_sound 14 39 5 cell_14_39_5
theorem cell_14_40_0 : CertificateAt 14 40 0 := by decide +kernel
theorem cell_14_40_1 : CertificateAt 14 40 1 := by decide +kernel
theorem cell_14_40_2 : CertificateAt 14 40 2 := by decide +kernel
theorem cell_14_40_3 : CertificateAt 14 40 3 := by decide +kernel
theorem cell_14_40_4 : CertificateAt 14 40 4 := by decide +kernel
theorem cell_14_40_5 : CertificateAt 14 40 5 := by decide +kernel
theorem row_14_40 : ThresholdAt 14 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 40 0 cell_14_40_0
    | exact certificate_sound 14 40 1 cell_14_40_1
    | exact certificate_sound 14 40 2 cell_14_40_2
    | exact certificate_sound 14 40 3 cell_14_40_3
    | exact certificate_sound 14 40 4 cell_14_40_4
    | exact certificate_sound 14 40 5 cell_14_40_5
theorem cell_14_41_0 : CertificateAt 14 41 0 := by decide +kernel
theorem cell_14_41_1 : CertificateAt 14 41 1 := by decide +kernel
theorem cell_14_41_2 : CertificateAt 14 41 2 := by decide +kernel
theorem cell_14_41_3 : CertificateAt 14 41 3 := by decide +kernel
theorem cell_14_41_4 : CertificateAt 14 41 4 := by decide +kernel
theorem cell_14_41_5 : CertificateAt 14 41 5 := by decide +kernel
theorem row_14_41 : ThresholdAt 14 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 41 0 cell_14_41_0
    | exact certificate_sound 14 41 1 cell_14_41_1
    | exact certificate_sound 14 41 2 cell_14_41_2
    | exact certificate_sound 14 41 3 cell_14_41_3
    | exact certificate_sound 14 41 4 cell_14_41_4
    | exact certificate_sound 14 41 5 cell_14_41_5
theorem cell_14_42_0 : CertificateAt 14 42 0 := by decide +kernel
theorem cell_14_42_1 : CertificateAt 14 42 1 := by decide +kernel
theorem cell_14_42_2 : CertificateAt 14 42 2 := by decide +kernel
theorem cell_14_42_3 : CertificateAt 14 42 3 := by decide +kernel
theorem cell_14_42_4 : CertificateAt 14 42 4 := by decide +kernel
theorem cell_14_42_5 : CertificateAt 14 42 5 := by decide +kernel
theorem row_14_42 : ThresholdAt 14 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 42 0 cell_14_42_0
    | exact certificate_sound 14 42 1 cell_14_42_1
    | exact certificate_sound 14 42 2 cell_14_42_2
    | exact certificate_sound 14 42 3 cell_14_42_3
    | exact certificate_sound 14 42 4 cell_14_42_4
    | exact certificate_sound 14 42 5 cell_14_42_5
theorem cell_14_43_0 : CertificateAt 14 43 0 := by decide +kernel
theorem cell_14_43_1 : CertificateAt 14 43 1 := by decide +kernel
theorem cell_14_43_2 : CertificateAt 14 43 2 := by decide +kernel
theorem cell_14_43_3 : CertificateAt 14 43 3 := by decide +kernel
theorem cell_14_43_4 : CertificateAt 14 43 4 := by decide +kernel
theorem cell_14_43_5 : CertificateAt 14 43 5 := by decide +kernel
theorem row_14_43 : ThresholdAt 14 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 43 0 cell_14_43_0
    | exact certificate_sound 14 43 1 cell_14_43_1
    | exact certificate_sound 14 43 2 cell_14_43_2
    | exact certificate_sound 14 43 3 cell_14_43_3
    | exact certificate_sound 14 43 4 cell_14_43_4
    | exact certificate_sound 14 43 5 cell_14_43_5
theorem cell_14_44_0 : CertificateAt 14 44 0 := by decide +kernel
theorem cell_14_44_1 : CertificateAt 14 44 1 := by decide +kernel
theorem cell_14_44_2 : CertificateAt 14 44 2 := by decide +kernel
theorem cell_14_44_3 : CertificateAt 14 44 3 := by decide +kernel
theorem cell_14_44_4 : CertificateAt 14 44 4 := by decide +kernel
theorem cell_14_44_5 : CertificateAt 14 44 5 := by decide +kernel
theorem row_14_44 : ThresholdAt 14 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 44 0 cell_14_44_0
    | exact certificate_sound 14 44 1 cell_14_44_1
    | exact certificate_sound 14 44 2 cell_14_44_2
    | exact certificate_sound 14 44 3 cell_14_44_3
    | exact certificate_sound 14 44 4 cell_14_44_4
    | exact certificate_sound 14 44 5 cell_14_44_5
theorem cell_14_45_0 : CertificateAt 14 45 0 := by decide +kernel
theorem cell_14_45_1 : CertificateAt 14 45 1 := by decide +kernel
theorem cell_14_45_2 : CertificateAt 14 45 2 := by decide +kernel
theorem cell_14_45_3 : CertificateAt 14 45 3 := by decide +kernel
theorem cell_14_45_4 : CertificateAt 14 45 4 := by decide +kernel
theorem cell_14_45_5 : CertificateAt 14 45 5 := by decide +kernel
theorem row_14_45 : ThresholdAt 14 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 45 0 cell_14_45_0
    | exact certificate_sound 14 45 1 cell_14_45_1
    | exact certificate_sound 14 45 2 cell_14_45_2
    | exact certificate_sound 14 45 3 cell_14_45_3
    | exact certificate_sound 14 45 4 cell_14_45_4
    | exact certificate_sound 14 45 5 cell_14_45_5
theorem cell_14_46_0 : CertificateAt 14 46 0 := by decide +kernel
theorem cell_14_46_1 : CertificateAt 14 46 1 := by decide +kernel
theorem cell_14_46_2 : CertificateAt 14 46 2 := by decide +kernel
theorem cell_14_46_3 : CertificateAt 14 46 3 := by decide +kernel
theorem cell_14_46_4 : CertificateAt 14 46 4 := by decide +kernel
theorem cell_14_46_5 : CertificateAt 14 46 5 := by decide +kernel
theorem row_14_46 : ThresholdAt 14 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 46 0 cell_14_46_0
    | exact certificate_sound 14 46 1 cell_14_46_1
    | exact certificate_sound 14 46 2 cell_14_46_2
    | exact certificate_sound 14 46 3 cell_14_46_3
    | exact certificate_sound 14 46 4 cell_14_46_4
    | exact certificate_sound 14 46 5 cell_14_46_5
theorem cell_14_47_0 : CertificateAt 14 47 0 := by decide +kernel
theorem cell_14_47_1 : CertificateAt 14 47 1 := by decide +kernel
theorem cell_14_47_2 : CertificateAt 14 47 2 := by decide +kernel
theorem cell_14_47_3 : CertificateAt 14 47 3 := by decide +kernel
theorem cell_14_47_4 : CertificateAt 14 47 4 := by decide +kernel
theorem cell_14_47_5 : CertificateAt 14 47 5 := by decide +kernel
theorem row_14_47 : ThresholdAt 14 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 47 0 cell_14_47_0
    | exact certificate_sound 14 47 1 cell_14_47_1
    | exact certificate_sound 14 47 2 cell_14_47_2
    | exact certificate_sound 14 47 3 cell_14_47_3
    | exact certificate_sound 14 47 4 cell_14_47_4
    | exact certificate_sound 14 47 5 cell_14_47_5
theorem cell_14_48_0 : CertificateAt 14 48 0 := by decide +kernel
theorem cell_14_48_1 : CertificateAt 14 48 1 := by decide +kernel
theorem cell_14_48_2 : CertificateAt 14 48 2 := by decide +kernel
theorem cell_14_48_3 : CertificateAt 14 48 3 := by decide +kernel
theorem cell_14_48_4 : CertificateAt 14 48 4 := by decide +kernel
theorem cell_14_48_5 : CertificateAt 14 48 5 := by decide +kernel
theorem row_14_48 : ThresholdAt 14 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 48 0 cell_14_48_0
    | exact certificate_sound 14 48 1 cell_14_48_1
    | exact certificate_sound 14 48 2 cell_14_48_2
    | exact certificate_sound 14 48 3 cell_14_48_3
    | exact certificate_sound 14 48 4 cell_14_48_4
    | exact certificate_sound 14 48 5 cell_14_48_5
theorem cell_14_49_0 : CertificateAt 14 49 0 := by decide +kernel
theorem cell_14_49_1 : CertificateAt 14 49 1 := by decide +kernel
theorem cell_14_49_2 : CertificateAt 14 49 2 := by decide +kernel
theorem cell_14_49_3 : CertificateAt 14 49 3 := by decide +kernel
theorem cell_14_49_4 : CertificateAt 14 49 4 := by decide +kernel
theorem cell_14_49_5 : CertificateAt 14 49 5 := by decide +kernel
theorem row_14_49 : ThresholdAt 14 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 49 0 cell_14_49_0
    | exact certificate_sound 14 49 1 cell_14_49_1
    | exact certificate_sound 14 49 2 cell_14_49_2
    | exact certificate_sound 14 49 3 cell_14_49_3
    | exact certificate_sound 14 49 4 cell_14_49_4
    | exact certificate_sound 14 49 5 cell_14_49_5
theorem cell_14_50_0 : CertificateAt 14 50 0 := by decide +kernel
theorem cell_14_50_1 : CertificateAt 14 50 1 := by decide +kernel
theorem cell_14_50_2 : CertificateAt 14 50 2 := by decide +kernel
theorem cell_14_50_3 : CertificateAt 14 50 3 := by decide +kernel
theorem cell_14_50_4 : CertificateAt 14 50 4 := by decide +kernel
theorem cell_14_50_5 : CertificateAt 14 50 5 := by decide +kernel
theorem row_14_50 : ThresholdAt 14 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 50 0 cell_14_50_0
    | exact certificate_sound 14 50 1 cell_14_50_1
    | exact certificate_sound 14 50 2 cell_14_50_2
    | exact certificate_sound 14 50 3 cell_14_50_3
    | exact certificate_sound 14 50 4 cell_14_50_4
    | exact certificate_sound 14 50 5 cell_14_50_5
theorem cell_14_51_0 : CertificateAt 14 51 0 := by decide +kernel
theorem cell_14_51_1 : CertificateAt 14 51 1 := by decide +kernel
theorem cell_14_51_2 : CertificateAt 14 51 2 := by decide +kernel
theorem cell_14_51_3 : CertificateAt 14 51 3 := by decide +kernel
theorem cell_14_51_4 : CertificateAt 14 51 4 := by decide +kernel
theorem cell_14_51_5 : CertificateAt 14 51 5 := by decide +kernel
theorem row_14_51 : ThresholdAt 14 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 51 0 cell_14_51_0
    | exact certificate_sound 14 51 1 cell_14_51_1
    | exact certificate_sound 14 51 2 cell_14_51_2
    | exact certificate_sound 14 51 3 cell_14_51_3
    | exact certificate_sound 14 51 4 cell_14_51_4
    | exact certificate_sound 14 51 5 cell_14_51_5
theorem cell_14_52_0 : CertificateAt 14 52 0 := by decide +kernel
theorem cell_14_52_1 : CertificateAt 14 52 1 := by decide +kernel
theorem cell_14_52_2 : CertificateAt 14 52 2 := by decide +kernel
theorem cell_14_52_3 : CertificateAt 14 52 3 := by decide +kernel
theorem cell_14_52_4 : CertificateAt 14 52 4 := by decide +kernel
theorem cell_14_52_5 : CertificateAt 14 52 5 := by decide +kernel
theorem row_14_52 : ThresholdAt 14 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 52 0 cell_14_52_0
    | exact certificate_sound 14 52 1 cell_14_52_1
    | exact certificate_sound 14 52 2 cell_14_52_2
    | exact certificate_sound 14 52 3 cell_14_52_3
    | exact certificate_sound 14 52 4 cell_14_52_4
    | exact certificate_sound 14 52 5 cell_14_52_5
theorem cell_14_53_0 : CertificateAt 14 53 0 := by decide +kernel
theorem cell_14_53_1 : CertificateAt 14 53 1 := by decide +kernel
theorem cell_14_53_2 : CertificateAt 14 53 2 := by decide +kernel
theorem cell_14_53_3 : CertificateAt 14 53 3 := by decide +kernel
theorem cell_14_53_4 : CertificateAt 14 53 4 := by decide +kernel
theorem cell_14_53_5 : CertificateAt 14 53 5 := by decide +kernel
theorem row_14_53 : ThresholdAt 14 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 53 0 cell_14_53_0
    | exact certificate_sound 14 53 1 cell_14_53_1
    | exact certificate_sound 14 53 2 cell_14_53_2
    | exact certificate_sound 14 53 3 cell_14_53_3
    | exact certificate_sound 14 53 4 cell_14_53_4
    | exact certificate_sound 14 53 5 cell_14_53_5
theorem cell_14_54_0 : CertificateAt 14 54 0 := by decide +kernel
theorem cell_14_54_1 : CertificateAt 14 54 1 := by decide +kernel
theorem cell_14_54_2 : CertificateAt 14 54 2 := by decide +kernel
theorem cell_14_54_3 : CertificateAt 14 54 3 := by decide +kernel
theorem cell_14_54_4 : CertificateAt 14 54 4 := by decide +kernel
theorem cell_14_54_5 : CertificateAt 14 54 5 := by decide +kernel
theorem row_14_54 : ThresholdAt 14 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 54 0 cell_14_54_0
    | exact certificate_sound 14 54 1 cell_14_54_1
    | exact certificate_sound 14 54 2 cell_14_54_2
    | exact certificate_sound 14 54 3 cell_14_54_3
    | exact certificate_sound 14 54 4 cell_14_54_4
    | exact certificate_sound 14 54 5 cell_14_54_5
theorem cell_14_55_0 : CertificateAt 14 55 0 := by decide +kernel
theorem cell_14_55_1 : CertificateAt 14 55 1 := by decide +kernel
theorem cell_14_55_2 : CertificateAt 14 55 2 := by decide +kernel
theorem cell_14_55_3 : CertificateAt 14 55 3 := by decide +kernel
theorem cell_14_55_4 : CertificateAt 14 55 4 := by decide +kernel
theorem cell_14_55_5 : CertificateAt 14 55 5 := by decide +kernel
theorem row_14_55 : ThresholdAt 14 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 55 0 cell_14_55_0
    | exact certificate_sound 14 55 1 cell_14_55_1
    | exact certificate_sound 14 55 2 cell_14_55_2
    | exact certificate_sound 14 55 3 cell_14_55_3
    | exact certificate_sound 14 55 4 cell_14_55_4
    | exact certificate_sound 14 55 5 cell_14_55_5
theorem cell_14_56_0 : CertificateAt 14 56 0 := by decide +kernel
theorem cell_14_56_1 : CertificateAt 14 56 1 := by decide +kernel
theorem cell_14_56_2 : CertificateAt 14 56 2 := by decide +kernel
theorem cell_14_56_3 : CertificateAt 14 56 3 := by decide +kernel
theorem cell_14_56_4 : CertificateAt 14 56 4 := by decide +kernel
theorem cell_14_56_5 : CertificateAt 14 56 5 := by decide +kernel
theorem row_14_56 : ThresholdAt 14 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 56 0 cell_14_56_0
    | exact certificate_sound 14 56 1 cell_14_56_1
    | exact certificate_sound 14 56 2 cell_14_56_2
    | exact certificate_sound 14 56 3 cell_14_56_3
    | exact certificate_sound 14 56 4 cell_14_56_4
    | exact certificate_sound 14 56 5 cell_14_56_5
theorem cell_14_57_0 : CertificateAt 14 57 0 := by decide +kernel
theorem cell_14_57_1 : CertificateAt 14 57 1 := by decide +kernel
theorem cell_14_57_2 : CertificateAt 14 57 2 := by decide +kernel
theorem cell_14_57_3 : CertificateAt 14 57 3 := by decide +kernel
theorem cell_14_57_4 : CertificateAt 14 57 4 := by decide +kernel
theorem cell_14_57_5 : CertificateAt 14 57 5 := by decide +kernel
theorem row_14_57 : ThresholdAt 14 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 57 0 cell_14_57_0
    | exact certificate_sound 14 57 1 cell_14_57_1
    | exact certificate_sound 14 57 2 cell_14_57_2
    | exact certificate_sound 14 57 3 cell_14_57_3
    | exact certificate_sound 14 57 4 cell_14_57_4
    | exact certificate_sound 14 57 5 cell_14_57_5
theorem cell_14_58_0 : CertificateAt 14 58 0 := by decide +kernel
theorem cell_14_58_1 : CertificateAt 14 58 1 := by decide +kernel
theorem cell_14_58_2 : CertificateAt 14 58 2 := by decide +kernel
theorem cell_14_58_3 : CertificateAt 14 58 3 := by decide +kernel
theorem cell_14_58_4 : CertificateAt 14 58 4 := by decide +kernel
theorem cell_14_58_5 : CertificateAt 14 58 5 := by decide +kernel
theorem row_14_58 : ThresholdAt 14 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 58 0 cell_14_58_0
    | exact certificate_sound 14 58 1 cell_14_58_1
    | exact certificate_sound 14 58 2 cell_14_58_2
    | exact certificate_sound 14 58 3 cell_14_58_3
    | exact certificate_sound 14 58 4 cell_14_58_4
    | exact certificate_sound 14 58 5 cell_14_58_5
theorem cell_14_59_0 : CertificateAt 14 59 0 := by decide +kernel
theorem cell_14_59_1 : CertificateAt 14 59 1 := by decide +kernel
theorem cell_14_59_2 : CertificateAt 14 59 2 := by decide +kernel
theorem cell_14_59_3 : CertificateAt 14 59 3 := by decide +kernel
theorem cell_14_59_4 : CertificateAt 14 59 4 := by decide +kernel
theorem cell_14_59_5 : CertificateAt 14 59 5 := by decide +kernel
theorem row_14_59 : ThresholdAt 14 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 59 0 cell_14_59_0
    | exact certificate_sound 14 59 1 cell_14_59_1
    | exact certificate_sound 14 59 2 cell_14_59_2
    | exact certificate_sound 14 59 3 cell_14_59_3
    | exact certificate_sound 14 59 4 cell_14_59_4
    | exact certificate_sound 14 59 5 cell_14_59_5
theorem cell_14_60_0 : CertificateAt 14 60 0 := by decide +kernel
theorem cell_14_60_1 : CertificateAt 14 60 1 := by decide +kernel
theorem cell_14_60_2 : CertificateAt 14 60 2 := by decide +kernel
theorem cell_14_60_3 : CertificateAt 14 60 3 := by decide +kernel
theorem cell_14_60_4 : CertificateAt 14 60 4 := by decide +kernel
theorem cell_14_60_5 : CertificateAt 14 60 5 := by decide +kernel
theorem row_14_60 : ThresholdAt 14 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 60 0 cell_14_60_0
    | exact certificate_sound 14 60 1 cell_14_60_1
    | exact certificate_sound 14 60 2 cell_14_60_2
    | exact certificate_sound 14 60 3 cell_14_60_3
    | exact certificate_sound 14 60 4 cell_14_60_4
    | exact certificate_sound 14 60 5 cell_14_60_5
theorem cell_14_61_0 : CertificateAt 14 61 0 := by decide +kernel
theorem cell_14_61_1 : CertificateAt 14 61 1 := by decide +kernel
theorem cell_14_61_2 : CertificateAt 14 61 2 := by decide +kernel
theorem cell_14_61_3 : CertificateAt 14 61 3 := by decide +kernel
theorem cell_14_61_4 : CertificateAt 14 61 4 := by decide +kernel
theorem cell_14_61_5 : CertificateAt 14 61 5 := by decide +kernel
theorem row_14_61 : ThresholdAt 14 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 61 0 cell_14_61_0
    | exact certificate_sound 14 61 1 cell_14_61_1
    | exact certificate_sound 14 61 2 cell_14_61_2
    | exact certificate_sound 14 61 3 cell_14_61_3
    | exact certificate_sound 14 61 4 cell_14_61_4
    | exact certificate_sound 14 61 5 cell_14_61_5
theorem cell_14_62_0 : CertificateAt 14 62 0 := by decide +kernel
theorem cell_14_62_1 : CertificateAt 14 62 1 := by decide +kernel
theorem cell_14_62_2 : CertificateAt 14 62 2 := by decide +kernel
theorem cell_14_62_3 : CertificateAt 14 62 3 := by decide +kernel
theorem cell_14_62_4 : CertificateAt 14 62 4 := by decide +kernel
theorem cell_14_62_5 : CertificateAt 14 62 5 := by decide +kernel
theorem row_14_62 : ThresholdAt 14 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 62 0 cell_14_62_0
    | exact certificate_sound 14 62 1 cell_14_62_1
    | exact certificate_sound 14 62 2 cell_14_62_2
    | exact certificate_sound 14 62 3 cell_14_62_3
    | exact certificate_sound 14 62 4 cell_14_62_4
    | exact certificate_sound 14 62 5 cell_14_62_5
theorem cell_14_63_0 : CertificateAt 14 63 0 := by decide +kernel
theorem cell_14_63_1 : CertificateAt 14 63 1 := by decide +kernel
theorem cell_14_63_2 : CertificateAt 14 63 2 := by decide +kernel
theorem cell_14_63_3 : CertificateAt 14 63 3 := by decide +kernel
theorem cell_14_63_4 : CertificateAt 14 63 4 := by decide +kernel
theorem cell_14_63_5 : CertificateAt 14 63 5 := by decide +kernel
theorem row_14_63 : ThresholdAt 14 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 63 0 cell_14_63_0
    | exact certificate_sound 14 63 1 cell_14_63_1
    | exact certificate_sound 14 63 2 cell_14_63_2
    | exact certificate_sound 14 63 3 cell_14_63_3
    | exact certificate_sound 14 63 4 cell_14_63_4
    | exact certificate_sound 14 63 5 cell_14_63_5
theorem cell_14_64_0 : CertificateAt 14 64 0 := by decide +kernel
theorem cell_14_64_1 : CertificateAt 14 64 1 := by decide +kernel
theorem cell_14_64_2 : CertificateAt 14 64 2 := by decide +kernel
theorem cell_14_64_3 : CertificateAt 14 64 3 := by decide +kernel
theorem cell_14_64_4 : CertificateAt 14 64 4 := by decide +kernel
theorem cell_14_64_5 : CertificateAt 14 64 5 := by decide +kernel
theorem row_14_64 : ThresholdAt 14 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 64 0 cell_14_64_0
    | exact certificate_sound 14 64 1 cell_14_64_1
    | exact certificate_sound 14 64 2 cell_14_64_2
    | exact certificate_sound 14 64 3 cell_14_64_3
    | exact certificate_sound 14 64 4 cell_14_64_4
    | exact certificate_sound 14 64 5 cell_14_64_5
theorem cell_14_65_0 : CertificateAt 14 65 0 := by decide +kernel
theorem cell_14_65_1 : CertificateAt 14 65 1 := by decide +kernel
theorem cell_14_65_2 : CertificateAt 14 65 2 := by decide +kernel
theorem cell_14_65_3 : CertificateAt 14 65 3 := by decide +kernel
theorem cell_14_65_4 : CertificateAt 14 65 4 := by decide +kernel
theorem cell_14_65_5 : CertificateAt 14 65 5 := by decide +kernel
theorem row_14_65 : ThresholdAt 14 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 65 0 cell_14_65_0
    | exact certificate_sound 14 65 1 cell_14_65_1
    | exact certificate_sound 14 65 2 cell_14_65_2
    | exact certificate_sound 14 65 3 cell_14_65_3
    | exact certificate_sound 14 65 4 cell_14_65_4
    | exact certificate_sound 14 65 5 cell_14_65_5
theorem cell_14_66_0 : CertificateAt 14 66 0 := by decide +kernel
theorem cell_14_66_1 : CertificateAt 14 66 1 := by decide +kernel
theorem cell_14_66_2 : CertificateAt 14 66 2 := by decide +kernel
theorem cell_14_66_3 : CertificateAt 14 66 3 := by decide +kernel
theorem cell_14_66_4 : CertificateAt 14 66 4 := by decide +kernel
theorem cell_14_66_5 : CertificateAt 14 66 5 := by decide +kernel
theorem row_14_66 : ThresholdAt 14 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 66 0 cell_14_66_0
    | exact certificate_sound 14 66 1 cell_14_66_1
    | exact certificate_sound 14 66 2 cell_14_66_2
    | exact certificate_sound 14 66 3 cell_14_66_3
    | exact certificate_sound 14 66 4 cell_14_66_4
    | exact certificate_sound 14 66 5 cell_14_66_5
theorem cell_14_67_0 : CertificateAt 14 67 0 := by decide +kernel
theorem cell_14_67_1 : CertificateAt 14 67 1 := by decide +kernel
theorem cell_14_67_2 : CertificateAt 14 67 2 := by decide +kernel
theorem cell_14_67_3 : CertificateAt 14 67 3 := by decide +kernel
theorem cell_14_67_4 : CertificateAt 14 67 4 := by decide +kernel
theorem cell_14_67_5 : CertificateAt 14 67 5 := by decide +kernel
theorem row_14_67 : ThresholdAt 14 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 67 0 cell_14_67_0
    | exact certificate_sound 14 67 1 cell_14_67_1
    | exact certificate_sound 14 67 2 cell_14_67_2
    | exact certificate_sound 14 67 3 cell_14_67_3
    | exact certificate_sound 14 67 4 cell_14_67_4
    | exact certificate_sound 14 67 5 cell_14_67_5
theorem cell_14_68_0 : CertificateAt 14 68 0 := by decide +kernel
theorem cell_14_68_1 : CertificateAt 14 68 1 := by decide +kernel
theorem cell_14_68_2 : CertificateAt 14 68 2 := by decide +kernel
theorem cell_14_68_3 : CertificateAt 14 68 3 := by decide +kernel
theorem cell_14_68_4 : CertificateAt 14 68 4 := by decide +kernel
theorem cell_14_68_5 : CertificateAt 14 68 5 := by decide +kernel
theorem row_14_68 : ThresholdAt 14 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 68 0 cell_14_68_0
    | exact certificate_sound 14 68 1 cell_14_68_1
    | exact certificate_sound 14 68 2 cell_14_68_2
    | exact certificate_sound 14 68 3 cell_14_68_3
    | exact certificate_sound 14 68 4 cell_14_68_4
    | exact certificate_sound 14 68 5 cell_14_68_5
theorem cell_14_69_0 : CertificateAt 14 69 0 := by decide +kernel
theorem cell_14_69_1 : CertificateAt 14 69 1 := by decide +kernel
theorem cell_14_69_2 : CertificateAt 14 69 2 := by decide +kernel
theorem cell_14_69_3 : CertificateAt 14 69 3 := by decide +kernel
theorem cell_14_69_4 : CertificateAt 14 69 4 := by decide +kernel
theorem cell_14_69_5 : CertificateAt 14 69 5 := by decide +kernel
theorem row_14_69 : ThresholdAt 14 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 69 0 cell_14_69_0
    | exact certificate_sound 14 69 1 cell_14_69_1
    | exact certificate_sound 14 69 2 cell_14_69_2
    | exact certificate_sound 14 69 3 cell_14_69_3
    | exact certificate_sound 14 69 4 cell_14_69_4
    | exact certificate_sound 14 69 5 cell_14_69_5
theorem cell_14_70_0 : CertificateAt 14 70 0 := by decide +kernel
theorem cell_14_70_1 : CertificateAt 14 70 1 := by decide +kernel
theorem cell_14_70_2 : CertificateAt 14 70 2 := by decide +kernel
theorem cell_14_70_3 : CertificateAt 14 70 3 := by decide +kernel
theorem cell_14_70_4 : CertificateAt 14 70 4 := by decide +kernel
theorem cell_14_70_5 : CertificateAt 14 70 5 := by decide +kernel
theorem row_14_70 : ThresholdAt 14 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 70 0 cell_14_70_0
    | exact certificate_sound 14 70 1 cell_14_70_1
    | exact certificate_sound 14 70 2 cell_14_70_2
    | exact certificate_sound 14 70 3 cell_14_70_3
    | exact certificate_sound 14 70 4 cell_14_70_4
    | exact certificate_sound 14 70 5 cell_14_70_5
theorem cell_14_71_0 : CertificateAt 14 71 0 := by decide +kernel
theorem cell_14_71_1 : CertificateAt 14 71 1 := by decide +kernel
theorem cell_14_71_2 : CertificateAt 14 71 2 := by decide +kernel
theorem cell_14_71_3 : CertificateAt 14 71 3 := by decide +kernel
theorem cell_14_71_4 : CertificateAt 14 71 4 := by decide +kernel
theorem cell_14_71_5 : CertificateAt 14 71 5 := by decide +kernel
theorem row_14_71 : ThresholdAt 14 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 71 0 cell_14_71_0
    | exact certificate_sound 14 71 1 cell_14_71_1
    | exact certificate_sound 14 71 2 cell_14_71_2
    | exact certificate_sound 14 71 3 cell_14_71_3
    | exact certificate_sound 14 71 4 cell_14_71_4
    | exact certificate_sound 14 71 5 cell_14_71_5
theorem cell_14_72_0 : CertificateAt 14 72 0 := by decide +kernel
theorem cell_14_72_1 : CertificateAt 14 72 1 := by decide +kernel
theorem cell_14_72_2 : CertificateAt 14 72 2 := by decide +kernel
theorem cell_14_72_3 : CertificateAt 14 72 3 := by decide +kernel
theorem cell_14_72_4 : CertificateAt 14 72 4 := by decide +kernel
theorem cell_14_72_5 : CertificateAt 14 72 5 := by decide +kernel
theorem row_14_72 : ThresholdAt 14 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 72 0 cell_14_72_0
    | exact certificate_sound 14 72 1 cell_14_72_1
    | exact certificate_sound 14 72 2 cell_14_72_2
    | exact certificate_sound 14 72 3 cell_14_72_3
    | exact certificate_sound 14 72 4 cell_14_72_4
    | exact certificate_sound 14 72 5 cell_14_72_5
theorem cell_14_73_0 : CertificateAt 14 73 0 := by decide +kernel
theorem cell_14_73_1 : CertificateAt 14 73 1 := by decide +kernel
theorem cell_14_73_2 : CertificateAt 14 73 2 := by decide +kernel
theorem cell_14_73_3 : CertificateAt 14 73 3 := by decide +kernel
theorem cell_14_73_4 : CertificateAt 14 73 4 := by decide +kernel
theorem cell_14_73_5 : CertificateAt 14 73 5 := by decide +kernel
theorem row_14_73 : ThresholdAt 14 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 73 0 cell_14_73_0
    | exact certificate_sound 14 73 1 cell_14_73_1
    | exact certificate_sound 14 73 2 cell_14_73_2
    | exact certificate_sound 14 73 3 cell_14_73_3
    | exact certificate_sound 14 73 4 cell_14_73_4
    | exact certificate_sound 14 73 5 cell_14_73_5
theorem cell_14_74_0 : CertificateAt 14 74 0 := by decide +kernel
theorem cell_14_74_1 : CertificateAt 14 74 1 := by decide +kernel
theorem cell_14_74_2 : CertificateAt 14 74 2 := by decide +kernel
theorem cell_14_74_3 : CertificateAt 14 74 3 := by decide +kernel
theorem cell_14_74_4 : CertificateAt 14 74 4 := by decide +kernel
theorem cell_14_74_5 : CertificateAt 14 74 5 := by decide +kernel
theorem row_14_74 : ThresholdAt 14 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 74 0 cell_14_74_0
    | exact certificate_sound 14 74 1 cell_14_74_1
    | exact certificate_sound 14 74 2 cell_14_74_2
    | exact certificate_sound 14 74 3 cell_14_74_3
    | exact certificate_sound 14 74 4 cell_14_74_4
    | exact certificate_sound 14 74 5 cell_14_74_5
theorem cell_14_75_0 : CertificateAt 14 75 0 := by decide +kernel
theorem cell_14_75_1 : CertificateAt 14 75 1 := by decide +kernel
theorem cell_14_75_2 : CertificateAt 14 75 2 := by decide +kernel
theorem cell_14_75_3 : CertificateAt 14 75 3 := by decide +kernel
theorem cell_14_75_4 : CertificateAt 14 75 4 := by decide +kernel
theorem cell_14_75_5 : CertificateAt 14 75 5 := by decide +kernel
theorem row_14_75 : ThresholdAt 14 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 75 0 cell_14_75_0
    | exact certificate_sound 14 75 1 cell_14_75_1
    | exact certificate_sound 14 75 2 cell_14_75_2
    | exact certificate_sound 14 75 3 cell_14_75_3
    | exact certificate_sound 14 75 4 cell_14_75_4
    | exact certificate_sound 14 75 5 cell_14_75_5
theorem cell_14_76_0 : CertificateAt 14 76 0 := by decide +kernel
theorem cell_14_76_1 : CertificateAt 14 76 1 := by decide +kernel
theorem cell_14_76_2 : CertificateAt 14 76 2 := by decide +kernel
theorem cell_14_76_3 : CertificateAt 14 76 3 := by decide +kernel
theorem cell_14_76_4 : CertificateAt 14 76 4 := by decide +kernel
theorem cell_14_76_5 : CertificateAt 14 76 5 := by decide +kernel
theorem row_14_76 : ThresholdAt 14 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 76 0 cell_14_76_0
    | exact certificate_sound 14 76 1 cell_14_76_1
    | exact certificate_sound 14 76 2 cell_14_76_2
    | exact certificate_sound 14 76 3 cell_14_76_3
    | exact certificate_sound 14 76 4 cell_14_76_4
    | exact certificate_sound 14 76 5 cell_14_76_5
theorem cell_14_77_0 : CertificateAt 14 77 0 := by decide +kernel
theorem cell_14_77_1 : CertificateAt 14 77 1 := by decide +kernel
theorem cell_14_77_2 : CertificateAt 14 77 2 := by decide +kernel
theorem cell_14_77_3 : CertificateAt 14 77 3 := by decide +kernel
theorem cell_14_77_4 : CertificateAt 14 77 4 := by decide +kernel
theorem cell_14_77_5 : CertificateAt 14 77 5 := by decide +kernel
theorem row_14_77 : ThresholdAt 14 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 77 0 cell_14_77_0
    | exact certificate_sound 14 77 1 cell_14_77_1
    | exact certificate_sound 14 77 2 cell_14_77_2
    | exact certificate_sound 14 77 3 cell_14_77_3
    | exact certificate_sound 14 77 4 cell_14_77_4
    | exact certificate_sound 14 77 5 cell_14_77_5
theorem cell_14_78_0 : CertificateAt 14 78 0 := by decide +kernel
theorem cell_14_78_1 : CertificateAt 14 78 1 := by decide +kernel
theorem cell_14_78_2 : CertificateAt 14 78 2 := by decide +kernel
theorem cell_14_78_3 : CertificateAt 14 78 3 := by decide +kernel
theorem cell_14_78_4 : CertificateAt 14 78 4 := by decide +kernel
theorem cell_14_78_5 : CertificateAt 14 78 5 := by decide +kernel
theorem row_14_78 : ThresholdAt 14 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 78 0 cell_14_78_0
    | exact certificate_sound 14 78 1 cell_14_78_1
    | exact certificate_sound 14 78 2 cell_14_78_2
    | exact certificate_sound 14 78 3 cell_14_78_3
    | exact certificate_sound 14 78 4 cell_14_78_4
    | exact certificate_sound 14 78 5 cell_14_78_5
theorem cell_14_79_0 : CertificateAt 14 79 0 := by decide +kernel
theorem cell_14_79_1 : CertificateAt 14 79 1 := by decide +kernel
theorem cell_14_79_2 : CertificateAt 14 79 2 := by decide +kernel
theorem cell_14_79_3 : CertificateAt 14 79 3 := by decide +kernel
theorem cell_14_79_4 : CertificateAt 14 79 4 := by decide +kernel
theorem cell_14_79_5 : CertificateAt 14 79 5 := by decide +kernel
theorem row_14_79 : ThresholdAt 14 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 79 0 cell_14_79_0
    | exact certificate_sound 14 79 1 cell_14_79_1
    | exact certificate_sound 14 79 2 cell_14_79_2
    | exact certificate_sound 14 79 3 cell_14_79_3
    | exact certificate_sound 14 79 4 cell_14_79_4
    | exact certificate_sound 14 79 5 cell_14_79_5
theorem cell_14_80_0 : CertificateAt 14 80 0 := by decide +kernel
theorem cell_14_80_1 : CertificateAt 14 80 1 := by decide +kernel
theorem cell_14_80_2 : CertificateAt 14 80 2 := by decide +kernel
theorem cell_14_80_3 : CertificateAt 14 80 3 := by decide +kernel
theorem cell_14_80_4 : CertificateAt 14 80 4 := by decide +kernel
theorem cell_14_80_5 : CertificateAt 14 80 5 := by decide +kernel
theorem row_14_80 : ThresholdAt 14 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 80 0 cell_14_80_0
    | exact certificate_sound 14 80 1 cell_14_80_1
    | exact certificate_sound 14 80 2 cell_14_80_2
    | exact certificate_sound 14 80 3 cell_14_80_3
    | exact certificate_sound 14 80 4 cell_14_80_4
    | exact certificate_sound 14 80 5 cell_14_80_5
theorem cell_14_81_0 : CertificateAt 14 81 0 := by decide +kernel
theorem cell_14_81_1 : CertificateAt 14 81 1 := by decide +kernel
theorem cell_14_81_2 : CertificateAt 14 81 2 := by decide +kernel
theorem cell_14_81_3 : CertificateAt 14 81 3 := by decide +kernel
theorem cell_14_81_4 : CertificateAt 14 81 4 := by decide +kernel
theorem cell_14_81_5 : CertificateAt 14 81 5 := by decide +kernel
theorem row_14_81 : ThresholdAt 14 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 81 0 cell_14_81_0
    | exact certificate_sound 14 81 1 cell_14_81_1
    | exact certificate_sound 14 81 2 cell_14_81_2
    | exact certificate_sound 14 81 3 cell_14_81_3
    | exact certificate_sound 14 81 4 cell_14_81_4
    | exact certificate_sound 14 81 5 cell_14_81_5
theorem cell_14_82_0 : CertificateAt 14 82 0 := by decide +kernel
theorem cell_14_82_1 : CertificateAt 14 82 1 := by decide +kernel
theorem cell_14_82_2 : CertificateAt 14 82 2 := by decide +kernel
theorem cell_14_82_3 : CertificateAt 14 82 3 := by decide +kernel
theorem cell_14_82_4 : CertificateAt 14 82 4 := by decide +kernel
theorem cell_14_82_5 : CertificateAt 14 82 5 := by decide +kernel
theorem row_14_82 : ThresholdAt 14 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 82 0 cell_14_82_0
    | exact certificate_sound 14 82 1 cell_14_82_1
    | exact certificate_sound 14 82 2 cell_14_82_2
    | exact certificate_sound 14 82 3 cell_14_82_3
    | exact certificate_sound 14 82 4 cell_14_82_4
    | exact certificate_sound 14 82 5 cell_14_82_5
theorem cell_14_83_0 : CertificateAt 14 83 0 := by decide +kernel
theorem cell_14_83_1 : CertificateAt 14 83 1 := by decide +kernel
theorem cell_14_83_2 : CertificateAt 14 83 2 := by decide +kernel
theorem cell_14_83_3 : CertificateAt 14 83 3 := by decide +kernel
theorem cell_14_83_4 : CertificateAt 14 83 4 := by decide +kernel
theorem cell_14_83_5 : CertificateAt 14 83 5 := by decide +kernel
theorem row_14_83 : ThresholdAt 14 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 83 0 cell_14_83_0
    | exact certificate_sound 14 83 1 cell_14_83_1
    | exact certificate_sound 14 83 2 cell_14_83_2
    | exact certificate_sound 14 83 3 cell_14_83_3
    | exact certificate_sound 14 83 4 cell_14_83_4
    | exact certificate_sound 14 83 5 cell_14_83_5
theorem cell_14_84_0 : CertificateAt 14 84 0 := by decide +kernel
theorem cell_14_84_1 : CertificateAt 14 84 1 := by decide +kernel
theorem cell_14_84_2 : CertificateAt 14 84 2 := by decide +kernel
theorem cell_14_84_3 : CertificateAt 14 84 3 := by decide +kernel
theorem cell_14_84_4 : CertificateAt 14 84 4 := by decide +kernel
theorem cell_14_84_5 : CertificateAt 14 84 5 := by decide +kernel
theorem row_14_84 : ThresholdAt 14 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 84 0 cell_14_84_0
    | exact certificate_sound 14 84 1 cell_14_84_1
    | exact certificate_sound 14 84 2 cell_14_84_2
    | exact certificate_sound 14 84 3 cell_14_84_3
    | exact certificate_sound 14 84 4 cell_14_84_4
    | exact certificate_sound 14 84 5 cell_14_84_5
theorem cell_14_85_0 : CertificateAt 14 85 0 := by decide +kernel
theorem cell_14_85_1 : CertificateAt 14 85 1 := by decide +kernel
theorem cell_14_85_2 : CertificateAt 14 85 2 := by decide +kernel
theorem cell_14_85_3 : CertificateAt 14 85 3 := by decide +kernel
theorem cell_14_85_4 : CertificateAt 14 85 4 := by decide +kernel
theorem cell_14_85_5 : CertificateAt 14 85 5 := by decide +kernel
theorem row_14_85 : ThresholdAt 14 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 85 0 cell_14_85_0
    | exact certificate_sound 14 85 1 cell_14_85_1
    | exact certificate_sound 14 85 2 cell_14_85_2
    | exact certificate_sound 14 85 3 cell_14_85_3
    | exact certificate_sound 14 85 4 cell_14_85_4
    | exact certificate_sound 14 85 5 cell_14_85_5
theorem cell_14_86_0 : CertificateAt 14 86 0 := by decide +kernel
theorem cell_14_86_1 : CertificateAt 14 86 1 := by decide +kernel
theorem cell_14_86_2 : CertificateAt 14 86 2 := by decide +kernel
theorem cell_14_86_3 : CertificateAt 14 86 3 := by decide +kernel
theorem cell_14_86_4 : CertificateAt 14 86 4 := by decide +kernel
theorem cell_14_86_5 : CertificateAt 14 86 5 := by decide +kernel
theorem row_14_86 : ThresholdAt 14 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 86 0 cell_14_86_0
    | exact certificate_sound 14 86 1 cell_14_86_1
    | exact certificate_sound 14 86 2 cell_14_86_2
    | exact certificate_sound 14 86 3 cell_14_86_3
    | exact certificate_sound 14 86 4 cell_14_86_4
    | exact certificate_sound 14 86 5 cell_14_86_5
theorem cell_14_87_0 : CertificateAt 14 87 0 := by decide +kernel
theorem cell_14_87_1 : CertificateAt 14 87 1 := by decide +kernel
theorem cell_14_87_2 : CertificateAt 14 87 2 := by decide +kernel
theorem cell_14_87_3 : CertificateAt 14 87 3 := by decide +kernel
theorem cell_14_87_4 : CertificateAt 14 87 4 := by decide +kernel
theorem cell_14_87_5 : CertificateAt 14 87 5 := by decide +kernel
theorem row_14_87 : ThresholdAt 14 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 87 0 cell_14_87_0
    | exact certificate_sound 14 87 1 cell_14_87_1
    | exact certificate_sound 14 87 2 cell_14_87_2
    | exact certificate_sound 14 87 3 cell_14_87_3
    | exact certificate_sound 14 87 4 cell_14_87_4
    | exact certificate_sound 14 87 5 cell_14_87_5
theorem cell_14_88_0 : CertificateAt 14 88 0 := by decide +kernel
theorem cell_14_88_1 : CertificateAt 14 88 1 := by decide +kernel
theorem cell_14_88_2 : CertificateAt 14 88 2 := by decide +kernel
theorem cell_14_88_3 : CertificateAt 14 88 3 := by decide +kernel
theorem cell_14_88_4 : CertificateAt 14 88 4 := by decide +kernel
theorem cell_14_88_5 : CertificateAt 14 88 5 := by decide +kernel
theorem row_14_88 : ThresholdAt 14 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 88 0 cell_14_88_0
    | exact certificate_sound 14 88 1 cell_14_88_1
    | exact certificate_sound 14 88 2 cell_14_88_2
    | exact certificate_sound 14 88 3 cell_14_88_3
    | exact certificate_sound 14 88 4 cell_14_88_4
    | exact certificate_sound 14 88 5 cell_14_88_5
theorem cell_14_89_0 : CertificateAt 14 89 0 := by decide +kernel
theorem cell_14_89_1 : CertificateAt 14 89 1 := by decide +kernel
theorem cell_14_89_2 : CertificateAt 14 89 2 := by decide +kernel
theorem cell_14_89_3 : CertificateAt 14 89 3 := by decide +kernel
theorem cell_14_89_4 : CertificateAt 14 89 4 := by decide +kernel
theorem cell_14_89_5 : CertificateAt 14 89 5 := by decide +kernel
theorem row_14_89 : ThresholdAt 14 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 89 0 cell_14_89_0
    | exact certificate_sound 14 89 1 cell_14_89_1
    | exact certificate_sound 14 89 2 cell_14_89_2
    | exact certificate_sound 14 89 3 cell_14_89_3
    | exact certificate_sound 14 89 4 cell_14_89_4
    | exact certificate_sound 14 89 5 cell_14_89_5
theorem cell_14_90_0 : CertificateAt 14 90 0 := by decide +kernel
theorem cell_14_90_1 : CertificateAt 14 90 1 := by decide +kernel
theorem cell_14_90_2 : CertificateAt 14 90 2 := by decide +kernel
theorem cell_14_90_3 : CertificateAt 14 90 3 := by decide +kernel
theorem cell_14_90_4 : CertificateAt 14 90 4 := by decide +kernel
theorem cell_14_90_5 : CertificateAt 14 90 5 := by decide +kernel
theorem row_14_90 : ThresholdAt 14 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 90 0 cell_14_90_0
    | exact certificate_sound 14 90 1 cell_14_90_1
    | exact certificate_sound 14 90 2 cell_14_90_2
    | exact certificate_sound 14 90 3 cell_14_90_3
    | exact certificate_sound 14 90 4 cell_14_90_4
    | exact certificate_sound 14 90 5 cell_14_90_5
theorem cell_14_91_0 : CertificateAt 14 91 0 := by decide +kernel
theorem cell_14_91_1 : CertificateAt 14 91 1 := by decide +kernel
theorem cell_14_91_2 : CertificateAt 14 91 2 := by decide +kernel
theorem cell_14_91_3 : CertificateAt 14 91 3 := by decide +kernel
theorem cell_14_91_4 : CertificateAt 14 91 4 := by decide +kernel
theorem cell_14_91_5 : CertificateAt 14 91 5 := by decide +kernel
theorem row_14_91 : ThresholdAt 14 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 91 0 cell_14_91_0
    | exact certificate_sound 14 91 1 cell_14_91_1
    | exact certificate_sound 14 91 2 cell_14_91_2
    | exact certificate_sound 14 91 3 cell_14_91_3
    | exact certificate_sound 14 91 4 cell_14_91_4
    | exact certificate_sound 14 91 5 cell_14_91_5
theorem cell_14_92_0 : CertificateAt 14 92 0 := by decide +kernel
theorem cell_14_92_1 : CertificateAt 14 92 1 := by decide +kernel
theorem cell_14_92_2 : CertificateAt 14 92 2 := by decide +kernel
theorem cell_14_92_3 : CertificateAt 14 92 3 := by decide +kernel
theorem cell_14_92_4 : CertificateAt 14 92 4 := by decide +kernel
theorem cell_14_92_5 : CertificateAt 14 92 5 := by decide +kernel
theorem row_14_92 : ThresholdAt 14 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 92 0 cell_14_92_0
    | exact certificate_sound 14 92 1 cell_14_92_1
    | exact certificate_sound 14 92 2 cell_14_92_2
    | exact certificate_sound 14 92 3 cell_14_92_3
    | exact certificate_sound 14 92 4 cell_14_92_4
    | exact certificate_sound 14 92 5 cell_14_92_5
theorem cell_14_93_0 : CertificateAt 14 93 0 := by decide +kernel
theorem cell_14_93_1 : CertificateAt 14 93 1 := by decide +kernel
theorem cell_14_93_2 : CertificateAt 14 93 2 := by decide +kernel
theorem cell_14_93_3 : CertificateAt 14 93 3 := by decide +kernel
theorem cell_14_93_4 : CertificateAt 14 93 4 := by decide +kernel
theorem cell_14_93_5 : CertificateAt 14 93 5 := by decide +kernel
theorem row_14_93 : ThresholdAt 14 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 93 0 cell_14_93_0
    | exact certificate_sound 14 93 1 cell_14_93_1
    | exact certificate_sound 14 93 2 cell_14_93_2
    | exact certificate_sound 14 93 3 cell_14_93_3
    | exact certificate_sound 14 93 4 cell_14_93_4
    | exact certificate_sound 14 93 5 cell_14_93_5
theorem cell_14_94_0 : CertificateAt 14 94 0 := by decide +kernel
theorem cell_14_94_1 : CertificateAt 14 94 1 := by decide +kernel
theorem cell_14_94_2 : CertificateAt 14 94 2 := by decide +kernel
theorem cell_14_94_3 : CertificateAt 14 94 3 := by decide +kernel
theorem cell_14_94_4 : CertificateAt 14 94 4 := by decide +kernel
theorem cell_14_94_5 : CertificateAt 14 94 5 := by decide +kernel
theorem row_14_94 : ThresholdAt 14 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 94 0 cell_14_94_0
    | exact certificate_sound 14 94 1 cell_14_94_1
    | exact certificate_sound 14 94 2 cell_14_94_2
    | exact certificate_sound 14 94 3 cell_14_94_3
    | exact certificate_sound 14 94 4 cell_14_94_4
    | exact certificate_sound 14 94 5 cell_14_94_5
theorem cell_14_95_0 : CertificateAt 14 95 0 := by decide +kernel
theorem cell_14_95_1 : CertificateAt 14 95 1 := by decide +kernel
theorem cell_14_95_2 : CertificateAt 14 95 2 := by decide +kernel
theorem cell_14_95_3 : CertificateAt 14 95 3 := by decide +kernel
theorem cell_14_95_4 : CertificateAt 14 95 4 := by decide +kernel
theorem cell_14_95_5 : CertificateAt 14 95 5 := by decide +kernel
theorem row_14_95 : ThresholdAt 14 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 95 0 cell_14_95_0
    | exact certificate_sound 14 95 1 cell_14_95_1
    | exact certificate_sound 14 95 2 cell_14_95_2
    | exact certificate_sound 14 95 3 cell_14_95_3
    | exact certificate_sound 14 95 4 cell_14_95_4
    | exact certificate_sound 14 95 5 cell_14_95_5
theorem cell_14_96_0 : CertificateAt 14 96 0 := by decide +kernel
theorem cell_14_96_1 : CertificateAt 14 96 1 := by decide +kernel
theorem cell_14_96_2 : CertificateAt 14 96 2 := by decide +kernel
theorem cell_14_96_3 : CertificateAt 14 96 3 := by decide +kernel
theorem cell_14_96_4 : CertificateAt 14 96 4 := by decide +kernel
theorem cell_14_96_5 : CertificateAt 14 96 5 := by decide +kernel
theorem row_14_96 : ThresholdAt 14 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 96 0 cell_14_96_0
    | exact certificate_sound 14 96 1 cell_14_96_1
    | exact certificate_sound 14 96 2 cell_14_96_2
    | exact certificate_sound 14 96 3 cell_14_96_3
    | exact certificate_sound 14 96 4 cell_14_96_4
    | exact certificate_sound 14 96 5 cell_14_96_5
theorem cell_14_97_0 : CertificateAt 14 97 0 := by decide +kernel
theorem cell_14_97_1 : CertificateAt 14 97 1 := by decide +kernel
theorem cell_14_97_2 : CertificateAt 14 97 2 := by decide +kernel
theorem cell_14_97_3 : CertificateAt 14 97 3 := by decide +kernel
theorem cell_14_97_4 : CertificateAt 14 97 4 := by decide +kernel
theorem cell_14_97_5 : CertificateAt 14 97 5 := by decide +kernel
theorem row_14_97 : ThresholdAt 14 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 97 0 cell_14_97_0
    | exact certificate_sound 14 97 1 cell_14_97_1
    | exact certificate_sound 14 97 2 cell_14_97_2
    | exact certificate_sound 14 97 3 cell_14_97_3
    | exact certificate_sound 14 97 4 cell_14_97_4
    | exact certificate_sound 14 97 5 cell_14_97_5
theorem cell_14_98_0 : CertificateAt 14 98 0 := by decide +kernel
theorem cell_14_98_1 : CertificateAt 14 98 1 := by decide +kernel
theorem cell_14_98_2 : CertificateAt 14 98 2 := by decide +kernel
theorem cell_14_98_3 : CertificateAt 14 98 3 := by decide +kernel
theorem cell_14_98_4 : CertificateAt 14 98 4 := by decide +kernel
theorem cell_14_98_5 : CertificateAt 14 98 5 := by decide +kernel
theorem row_14_98 : ThresholdAt 14 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 98 0 cell_14_98_0
    | exact certificate_sound 14 98 1 cell_14_98_1
    | exact certificate_sound 14 98 2 cell_14_98_2
    | exact certificate_sound 14 98 3 cell_14_98_3
    | exact certificate_sound 14 98 4 cell_14_98_4
    | exact certificate_sound 14 98 5 cell_14_98_5
theorem cell_14_99_0 : CertificateAt 14 99 0 := by decide +kernel
theorem cell_14_99_1 : CertificateAt 14 99 1 := by decide +kernel
theorem cell_14_99_2 : CertificateAt 14 99 2 := by decide +kernel
theorem cell_14_99_3 : CertificateAt 14 99 3 := by decide +kernel
theorem cell_14_99_4 : CertificateAt 14 99 4 := by decide +kernel
theorem cell_14_99_5 : CertificateAt 14 99 5 := by decide +kernel
theorem row_14_99 : ThresholdAt 14 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 99 0 cell_14_99_0
    | exact certificate_sound 14 99 1 cell_14_99_1
    | exact certificate_sound 14 99 2 cell_14_99_2
    | exact certificate_sound 14 99 3 cell_14_99_3
    | exact certificate_sound 14 99 4 cell_14_99_4
    | exact certificate_sound 14 99 5 cell_14_99_5
theorem cell_14_100_0 : CertificateAt 14 100 0 := by decide +kernel
theorem cell_14_100_1 : CertificateAt 14 100 1 := by decide +kernel
theorem cell_14_100_2 : CertificateAt 14 100 2 := by decide +kernel
theorem cell_14_100_3 : CertificateAt 14 100 3 := by decide +kernel
theorem cell_14_100_4 : CertificateAt 14 100 4 := by decide +kernel
theorem cell_14_100_5 : CertificateAt 14 100 5 := by decide +kernel
theorem row_14_100 : ThresholdAt 14 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 100 0 cell_14_100_0
    | exact certificate_sound 14 100 1 cell_14_100_1
    | exact certificate_sound 14 100 2 cell_14_100_2
    | exact certificate_sound 14 100 3 cell_14_100_3
    | exact certificate_sound 14 100 4 cell_14_100_4
    | exact certificate_sound 14 100 5 cell_14_100_5
theorem cell_14_101_0 : CertificateAt 14 101 0 := by decide +kernel
theorem cell_14_101_1 : CertificateAt 14 101 1 := by decide +kernel
theorem cell_14_101_2 : CertificateAt 14 101 2 := by decide +kernel
theorem cell_14_101_3 : CertificateAt 14 101 3 := by decide +kernel
theorem cell_14_101_4 : CertificateAt 14 101 4 := by decide +kernel
theorem cell_14_101_5 : CertificateAt 14 101 5 := by decide +kernel
theorem row_14_101 : ThresholdAt 14 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 101 0 cell_14_101_0
    | exact certificate_sound 14 101 1 cell_14_101_1
    | exact certificate_sound 14 101 2 cell_14_101_2
    | exact certificate_sound 14 101 3 cell_14_101_3
    | exact certificate_sound 14 101 4 cell_14_101_4
    | exact certificate_sound 14 101 5 cell_14_101_5
theorem cell_14_102_0 : CertificateAt 14 102 0 := by decide +kernel
theorem cell_14_102_1 : CertificateAt 14 102 1 := by decide +kernel
theorem cell_14_102_2 : CertificateAt 14 102 2 := by decide +kernel
theorem cell_14_102_3 : CertificateAt 14 102 3 := by decide +kernel
theorem cell_14_102_4 : CertificateAt 14 102 4 := by decide +kernel
theorem cell_14_102_5 : CertificateAt 14 102 5 := by decide +kernel
theorem row_14_102 : ThresholdAt 14 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 102 0 cell_14_102_0
    | exact certificate_sound 14 102 1 cell_14_102_1
    | exact certificate_sound 14 102 2 cell_14_102_2
    | exact certificate_sound 14 102 3 cell_14_102_3
    | exact certificate_sound 14 102 4 cell_14_102_4
    | exact certificate_sound 14 102 5 cell_14_102_5
theorem cell_14_103_0 : CertificateAt 14 103 0 := by decide +kernel
theorem cell_14_103_1 : CertificateAt 14 103 1 := by decide +kernel
theorem cell_14_103_2 : CertificateAt 14 103 2 := by decide +kernel
theorem cell_14_103_3 : CertificateAt 14 103 3 := by decide +kernel
theorem cell_14_103_4 : CertificateAt 14 103 4 := by decide +kernel
theorem cell_14_103_5 : CertificateAt 14 103 5 := by decide +kernel
theorem row_14_103 : ThresholdAt 14 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 103 0 cell_14_103_0
    | exact certificate_sound 14 103 1 cell_14_103_1
    | exact certificate_sound 14 103 2 cell_14_103_2
    | exact certificate_sound 14 103 3 cell_14_103_3
    | exact certificate_sound 14 103 4 cell_14_103_4
    | exact certificate_sound 14 103 5 cell_14_103_5
theorem cell_14_104_0 : CertificateAt 14 104 0 := by decide +kernel
theorem cell_14_104_1 : CertificateAt 14 104 1 := by decide +kernel
theorem cell_14_104_2 : CertificateAt 14 104 2 := by decide +kernel
theorem cell_14_104_3 : CertificateAt 14 104 3 := by decide +kernel
theorem cell_14_104_4 : CertificateAt 14 104 4 := by decide +kernel
theorem cell_14_104_5 : CertificateAt 14 104 5 := by decide +kernel
theorem row_14_104 : ThresholdAt 14 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 104 0 cell_14_104_0
    | exact certificate_sound 14 104 1 cell_14_104_1
    | exact certificate_sound 14 104 2 cell_14_104_2
    | exact certificate_sound 14 104 3 cell_14_104_3
    | exact certificate_sound 14 104 4 cell_14_104_4
    | exact certificate_sound 14 104 5 cell_14_104_5
theorem cell_14_105_0 : CertificateAt 14 105 0 := by decide +kernel
theorem cell_14_105_1 : CertificateAt 14 105 1 := by decide +kernel
theorem cell_14_105_2 : CertificateAt 14 105 2 := by decide +kernel
theorem cell_14_105_3 : CertificateAt 14 105 3 := by decide +kernel
theorem cell_14_105_4 : CertificateAt 14 105 4 := by decide +kernel
theorem cell_14_105_5 : CertificateAt 14 105 5 := by decide +kernel
theorem row_14_105 : ThresholdAt 14 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 105 0 cell_14_105_0
    | exact certificate_sound 14 105 1 cell_14_105_1
    | exact certificate_sound 14 105 2 cell_14_105_2
    | exact certificate_sound 14 105 3 cell_14_105_3
    | exact certificate_sound 14 105 4 cell_14_105_4
    | exact certificate_sound 14 105 5 cell_14_105_5
theorem cell_14_106_0 : CertificateAt 14 106 0 := by decide +kernel
theorem cell_14_106_1 : CertificateAt 14 106 1 := by decide +kernel
theorem cell_14_106_2 : CertificateAt 14 106 2 := by decide +kernel
theorem cell_14_106_3 : CertificateAt 14 106 3 := by decide +kernel
theorem cell_14_106_4 : CertificateAt 14 106 4 := by decide +kernel
theorem cell_14_106_5 : CertificateAt 14 106 5 := by decide +kernel
theorem row_14_106 : ThresholdAt 14 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 106 0 cell_14_106_0
    | exact certificate_sound 14 106 1 cell_14_106_1
    | exact certificate_sound 14 106 2 cell_14_106_2
    | exact certificate_sound 14 106 3 cell_14_106_3
    | exact certificate_sound 14 106 4 cell_14_106_4
    | exact certificate_sound 14 106 5 cell_14_106_5
theorem cell_14_107_0 : CertificateAt 14 107 0 := by decide +kernel
theorem cell_14_107_1 : CertificateAt 14 107 1 := by decide +kernel
theorem cell_14_107_2 : CertificateAt 14 107 2 := by decide +kernel
theorem cell_14_107_3 : CertificateAt 14 107 3 := by decide +kernel
theorem cell_14_107_4 : CertificateAt 14 107 4 := by decide +kernel
theorem cell_14_107_5 : CertificateAt 14 107 5 := by decide +kernel
theorem row_14_107 : ThresholdAt 14 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 107 0 cell_14_107_0
    | exact certificate_sound 14 107 1 cell_14_107_1
    | exact certificate_sound 14 107 2 cell_14_107_2
    | exact certificate_sound 14 107 3 cell_14_107_3
    | exact certificate_sound 14 107 4 cell_14_107_4
    | exact certificate_sound 14 107 5 cell_14_107_5
theorem cell_14_108_0 : CertificateAt 14 108 0 := by decide +kernel
theorem cell_14_108_1 : CertificateAt 14 108 1 := by decide +kernel
theorem cell_14_108_2 : CertificateAt 14 108 2 := by decide +kernel
theorem cell_14_108_3 : CertificateAt 14 108 3 := by decide +kernel
theorem cell_14_108_4 : CertificateAt 14 108 4 := by decide +kernel
theorem cell_14_108_5 : CertificateAt 14 108 5 := by decide +kernel
theorem row_14_108 : ThresholdAt 14 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 108 0 cell_14_108_0
    | exact certificate_sound 14 108 1 cell_14_108_1
    | exact certificate_sound 14 108 2 cell_14_108_2
    | exact certificate_sound 14 108 3 cell_14_108_3
    | exact certificate_sound 14 108 4 cell_14_108_4
    | exact certificate_sound 14 108 5 cell_14_108_5
theorem cell_14_109_0 : CertificateAt 14 109 0 := by decide +kernel
theorem cell_14_109_1 : CertificateAt 14 109 1 := by decide +kernel
theorem cell_14_109_2 : CertificateAt 14 109 2 := by decide +kernel
theorem cell_14_109_3 : CertificateAt 14 109 3 := by decide +kernel
theorem cell_14_109_4 : CertificateAt 14 109 4 := by decide +kernel
theorem cell_14_109_5 : CertificateAt 14 109 5 := by decide +kernel
theorem row_14_109 : ThresholdAt 14 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 109 0 cell_14_109_0
    | exact certificate_sound 14 109 1 cell_14_109_1
    | exact certificate_sound 14 109 2 cell_14_109_2
    | exact certificate_sound 14 109 3 cell_14_109_3
    | exact certificate_sound 14 109 4 cell_14_109_4
    | exact certificate_sound 14 109 5 cell_14_109_5
theorem cell_14_110_0 : CertificateAt 14 110 0 := by decide +kernel
theorem cell_14_110_1 : CertificateAt 14 110 1 := by decide +kernel
theorem cell_14_110_2 : CertificateAt 14 110 2 := by decide +kernel
theorem cell_14_110_3 : CertificateAt 14 110 3 := by decide +kernel
theorem cell_14_110_4 : CertificateAt 14 110 4 := by decide +kernel
theorem cell_14_110_5 : CertificateAt 14 110 5 := by decide +kernel
theorem row_14_110 : ThresholdAt 14 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 110 0 cell_14_110_0
    | exact certificate_sound 14 110 1 cell_14_110_1
    | exact certificate_sound 14 110 2 cell_14_110_2
    | exact certificate_sound 14 110 3 cell_14_110_3
    | exact certificate_sound 14 110 4 cell_14_110_4
    | exact certificate_sound 14 110 5 cell_14_110_5
theorem cell_14_111_0 : CertificateAt 14 111 0 := by decide +kernel
theorem cell_14_111_1 : CertificateAt 14 111 1 := by decide +kernel
theorem cell_14_111_2 : CertificateAt 14 111 2 := by decide +kernel
theorem cell_14_111_3 : CertificateAt 14 111 3 := by decide +kernel
theorem cell_14_111_4 : CertificateAt 14 111 4 := by decide +kernel
theorem cell_14_111_5 : CertificateAt 14 111 5 := by decide +kernel
theorem row_14_111 : ThresholdAt 14 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 111 0 cell_14_111_0
    | exact certificate_sound 14 111 1 cell_14_111_1
    | exact certificate_sound 14 111 2 cell_14_111_2
    | exact certificate_sound 14 111 3 cell_14_111_3
    | exact certificate_sound 14 111 4 cell_14_111_4
    | exact certificate_sound 14 111 5 cell_14_111_5
theorem cell_14_112_0 : CertificateAt 14 112 0 := by decide +kernel
theorem cell_14_112_1 : CertificateAt 14 112 1 := by decide +kernel
theorem cell_14_112_2 : CertificateAt 14 112 2 := by decide +kernel
theorem cell_14_112_3 : CertificateAt 14 112 3 := by decide +kernel
theorem cell_14_112_4 : CertificateAt 14 112 4 := by decide +kernel
theorem cell_14_112_5 : CertificateAt 14 112 5 := by decide +kernel
theorem row_14_112 : ThresholdAt 14 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 112 0 cell_14_112_0
    | exact certificate_sound 14 112 1 cell_14_112_1
    | exact certificate_sound 14 112 2 cell_14_112_2
    | exact certificate_sound 14 112 3 cell_14_112_3
    | exact certificate_sound 14 112 4 cell_14_112_4
    | exact certificate_sound 14 112 5 cell_14_112_5
theorem cell_14_113_0 : CertificateAt 14 113 0 := by decide +kernel
theorem cell_14_113_1 : CertificateAt 14 113 1 := by decide +kernel
theorem cell_14_113_2 : CertificateAt 14 113 2 := by decide +kernel
theorem cell_14_113_3 : CertificateAt 14 113 3 := by decide +kernel
theorem cell_14_113_4 : CertificateAt 14 113 4 := by decide +kernel
theorem cell_14_113_5 : CertificateAt 14 113 5 := by decide +kernel
theorem row_14_113 : ThresholdAt 14 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 113 0 cell_14_113_0
    | exact certificate_sound 14 113 1 cell_14_113_1
    | exact certificate_sound 14 113 2 cell_14_113_2
    | exact certificate_sound 14 113 3 cell_14_113_3
    | exact certificate_sound 14 113 4 cell_14_113_4
    | exact certificate_sound 14 113 5 cell_14_113_5
theorem cell_14_114_0 : CertificateAt 14 114 0 := by decide +kernel
theorem cell_14_114_1 : CertificateAt 14 114 1 := by decide +kernel
theorem cell_14_114_2 : CertificateAt 14 114 2 := by decide +kernel
theorem cell_14_114_3 : CertificateAt 14 114 3 := by decide +kernel
theorem cell_14_114_4 : CertificateAt 14 114 4 := by decide +kernel
theorem cell_14_114_5 : CertificateAt 14 114 5 := by decide +kernel
theorem row_14_114 : ThresholdAt 14 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 114 0 cell_14_114_0
    | exact certificate_sound 14 114 1 cell_14_114_1
    | exact certificate_sound 14 114 2 cell_14_114_2
    | exact certificate_sound 14 114 3 cell_14_114_3
    | exact certificate_sound 14 114 4 cell_14_114_4
    | exact certificate_sound 14 114 5 cell_14_114_5
theorem cell_14_115_0 : CertificateAt 14 115 0 := by decide +kernel
theorem cell_14_115_1 : CertificateAt 14 115 1 := by decide +kernel
theorem cell_14_115_2 : CertificateAt 14 115 2 := by decide +kernel
theorem cell_14_115_3 : CertificateAt 14 115 3 := by decide +kernel
theorem cell_14_115_4 : CertificateAt 14 115 4 := by decide +kernel
theorem cell_14_115_5 : CertificateAt 14 115 5 := by decide +kernel
theorem row_14_115 : ThresholdAt 14 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 115 0 cell_14_115_0
    | exact certificate_sound 14 115 1 cell_14_115_1
    | exact certificate_sound 14 115 2 cell_14_115_2
    | exact certificate_sound 14 115 3 cell_14_115_3
    | exact certificate_sound 14 115 4 cell_14_115_4
    | exact certificate_sound 14 115 5 cell_14_115_5
theorem cell_14_116_0 : CertificateAt 14 116 0 := by decide +kernel
theorem cell_14_116_1 : CertificateAt 14 116 1 := by decide +kernel
theorem cell_14_116_2 : CertificateAt 14 116 2 := by decide +kernel
theorem cell_14_116_3 : CertificateAt 14 116 3 := by decide +kernel
theorem cell_14_116_4 : CertificateAt 14 116 4 := by decide +kernel
theorem cell_14_116_5 : CertificateAt 14 116 5 := by decide +kernel
theorem row_14_116 : ThresholdAt 14 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 116 0 cell_14_116_0
    | exact certificate_sound 14 116 1 cell_14_116_1
    | exact certificate_sound 14 116 2 cell_14_116_2
    | exact certificate_sound 14 116 3 cell_14_116_3
    | exact certificate_sound 14 116 4 cell_14_116_4
    | exact certificate_sound 14 116 5 cell_14_116_5
theorem cell_14_117_0 : CertificateAt 14 117 0 := by decide +kernel
theorem cell_14_117_1 : CertificateAt 14 117 1 := by decide +kernel
theorem cell_14_117_2 : CertificateAt 14 117 2 := by decide +kernel
theorem cell_14_117_3 : CertificateAt 14 117 3 := by decide +kernel
theorem cell_14_117_4 : CertificateAt 14 117 4 := by decide +kernel
theorem cell_14_117_5 : CertificateAt 14 117 5 := by decide +kernel
theorem row_14_117 : ThresholdAt 14 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 117 0 cell_14_117_0
    | exact certificate_sound 14 117 1 cell_14_117_1
    | exact certificate_sound 14 117 2 cell_14_117_2
    | exact certificate_sound 14 117 3 cell_14_117_3
    | exact certificate_sound 14 117 4 cell_14_117_4
    | exact certificate_sound 14 117 5 cell_14_117_5
theorem cell_14_118_0 : CertificateAt 14 118 0 := by decide +kernel
theorem cell_14_118_1 : CertificateAt 14 118 1 := by decide +kernel
theorem cell_14_118_2 : CertificateAt 14 118 2 := by decide +kernel
theorem cell_14_118_3 : CertificateAt 14 118 3 := by decide +kernel
theorem cell_14_118_4 : CertificateAt 14 118 4 := by decide +kernel
theorem cell_14_118_5 : CertificateAt 14 118 5 := by decide +kernel
theorem row_14_118 : ThresholdAt 14 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 118 0 cell_14_118_0
    | exact certificate_sound 14 118 1 cell_14_118_1
    | exact certificate_sound 14 118 2 cell_14_118_2
    | exact certificate_sound 14 118 3 cell_14_118_3
    | exact certificate_sound 14 118 4 cell_14_118_4
    | exact certificate_sound 14 118 5 cell_14_118_5
theorem cell_14_119_0 : CertificateAt 14 119 0 := by decide +kernel
theorem cell_14_119_1 : CertificateAt 14 119 1 := by decide +kernel
theorem cell_14_119_2 : CertificateAt 14 119 2 := by decide +kernel
theorem cell_14_119_3 : CertificateAt 14 119 3 := by decide +kernel
theorem cell_14_119_4 : CertificateAt 14 119 4 := by decide +kernel
theorem cell_14_119_5 : CertificateAt 14 119 5 := by decide +kernel
theorem row_14_119 : ThresholdAt 14 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 119 0 cell_14_119_0
    | exact certificate_sound 14 119 1 cell_14_119_1
    | exact certificate_sound 14 119 2 cell_14_119_2
    | exact certificate_sound 14 119 3 cell_14_119_3
    | exact certificate_sound 14 119 4 cell_14_119_4
    | exact certificate_sound 14 119 5 cell_14_119_5
theorem cell_14_120_0 : CertificateAt 14 120 0 := by decide +kernel
theorem cell_14_120_1 : CertificateAt 14 120 1 := by decide +kernel
theorem cell_14_120_2 : CertificateAt 14 120 2 := by decide +kernel
theorem cell_14_120_3 : CertificateAt 14 120 3 := by decide +kernel
theorem cell_14_120_4 : CertificateAt 14 120 4 := by decide +kernel
theorem cell_14_120_5 : CertificateAt 14 120 5 := by decide +kernel
theorem row_14_120 : ThresholdAt 14 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 120 0 cell_14_120_0
    | exact certificate_sound 14 120 1 cell_14_120_1
    | exact certificate_sound 14 120 2 cell_14_120_2
    | exact certificate_sound 14 120 3 cell_14_120_3
    | exact certificate_sound 14 120 4 cell_14_120_4
    | exact certificate_sound 14 120 5 cell_14_120_5
theorem cell_14_121_0 : CertificateAt 14 121 0 := by decide +kernel
theorem cell_14_121_1 : CertificateAt 14 121 1 := by decide +kernel
theorem cell_14_121_2 : CertificateAt 14 121 2 := by decide +kernel
theorem cell_14_121_3 : CertificateAt 14 121 3 := by decide +kernel
theorem cell_14_121_4 : CertificateAt 14 121 4 := by decide +kernel
theorem cell_14_121_5 : CertificateAt 14 121 5 := by decide +kernel
theorem row_14_121 : ThresholdAt 14 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 121 0 cell_14_121_0
    | exact certificate_sound 14 121 1 cell_14_121_1
    | exact certificate_sound 14 121 2 cell_14_121_2
    | exact certificate_sound 14 121 3 cell_14_121_3
    | exact certificate_sound 14 121 4 cell_14_121_4
    | exact certificate_sound 14 121 5 cell_14_121_5
theorem cell_14_122_0 : CertificateAt 14 122 0 := by decide +kernel
theorem cell_14_122_1 : CertificateAt 14 122 1 := by decide +kernel
theorem cell_14_122_2 : CertificateAt 14 122 2 := by decide +kernel
theorem cell_14_122_3 : CertificateAt 14 122 3 := by decide +kernel
theorem cell_14_122_4 : CertificateAt 14 122 4 := by decide +kernel
theorem cell_14_122_5 : CertificateAt 14 122 5 := by decide +kernel
theorem row_14_122 : ThresholdAt 14 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 122 0 cell_14_122_0
    | exact certificate_sound 14 122 1 cell_14_122_1
    | exact certificate_sound 14 122 2 cell_14_122_2
    | exact certificate_sound 14 122 3 cell_14_122_3
    | exact certificate_sound 14 122 4 cell_14_122_4
    | exact certificate_sound 14 122 5 cell_14_122_5
theorem cell_14_123_0 : CertificateAt 14 123 0 := by decide +kernel
theorem cell_14_123_1 : CertificateAt 14 123 1 := by decide +kernel
theorem cell_14_123_2 : CertificateAt 14 123 2 := by decide +kernel
theorem cell_14_123_3 : CertificateAt 14 123 3 := by decide +kernel
theorem cell_14_123_4 : CertificateAt 14 123 4 := by decide +kernel
theorem cell_14_123_5 : CertificateAt 14 123 5 := by decide +kernel
theorem row_14_123 : ThresholdAt 14 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 123 0 cell_14_123_0
    | exact certificate_sound 14 123 1 cell_14_123_1
    | exact certificate_sound 14 123 2 cell_14_123_2
    | exact certificate_sound 14 123 3 cell_14_123_3
    | exact certificate_sound 14 123 4 cell_14_123_4
    | exact certificate_sound 14 123 5 cell_14_123_5
theorem cell_14_124_0 : CertificateAt 14 124 0 := by decide +kernel
theorem cell_14_124_1 : CertificateAt 14 124 1 := by decide +kernel
theorem cell_14_124_2 : CertificateAt 14 124 2 := by decide +kernel
theorem cell_14_124_3 : CertificateAt 14 124 3 := by decide +kernel
theorem cell_14_124_4 : CertificateAt 14 124 4 := by decide +kernel
theorem cell_14_124_5 : CertificateAt 14 124 5 := by decide +kernel
theorem row_14_124 : ThresholdAt 14 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 124 0 cell_14_124_0
    | exact certificate_sound 14 124 1 cell_14_124_1
    | exact certificate_sound 14 124 2 cell_14_124_2
    | exact certificate_sound 14 124 3 cell_14_124_3
    | exact certificate_sound 14 124 4 cell_14_124_4
    | exact certificate_sound 14 124 5 cell_14_124_5
theorem cell_14_125_0 : CertificateAt 14 125 0 := by decide +kernel
theorem cell_14_125_1 : CertificateAt 14 125 1 := by decide +kernel
theorem cell_14_125_2 : CertificateAt 14 125 2 := by decide +kernel
theorem cell_14_125_3 : CertificateAt 14 125 3 := by decide +kernel
theorem cell_14_125_4 : CertificateAt 14 125 4 := by decide +kernel
theorem cell_14_125_5 : CertificateAt 14 125 5 := by decide +kernel
theorem row_14_125 : ThresholdAt 14 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 14 125 0 cell_14_125_0
    | exact certificate_sound 14 125 1 cell_14_125_1
    | exact certificate_sound 14 125 2 cell_14_125_2
    | exact certificate_sound 14 125 3 cell_14_125_3
    | exact certificate_sound 14 125 4 cell_14_125_4
    | exact certificate_sound 14 125 5 cell_14_125_5
theorem checkedR14 : ∀ V ∈ List.range 126, ThresholdAt 14 V := by
  intro V hV
  have hv : V < 126 := List.mem_range.mp hV
  by_cases h0_126 : V < 63
  · by_cases h0_63 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_14_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_14_1
              · have he : V = 2 := by omega
                subst V
                exact row_14_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_14_3
              · have he : V = 4 := by omega
                subst V
                exact row_14_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_14_5
              · have he : V = 6 := by omega
                subst V
                exact row_14_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_14_7
              · have he : V = 8 := by omega
                subst V
                exact row_14_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_14_9
              · have he : V = 10 := by omega
                subst V
                exact row_14_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_14_11
              · have he : V = 12 := by omega
                subst V
                exact row_14_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_14_13
              · have he : V = 14 := by omega
                subst V
                exact row_14_14
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_14_15
              · have he : V = 16 := by omega
                subst V
                exact row_14_16
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_14_17
              · have he : V = 18 := by omega
                subst V
                exact row_14_18
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_14_19
              · have he : V = 20 := by omega
                subst V
                exact row_14_20
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_14_21
              · have he : V = 22 := by omega
                subst V
                exact row_14_22
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_14_23
              · have he : V = 24 := by omega
                subst V
                exact row_14_24
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_14_25
              · have he : V = 26 := by omega
                subst V
                exact row_14_26
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_14_27
              · have he : V = 28 := by omega
                subst V
                exact row_14_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_14_29
              · have he : V = 30 := by omega
                subst V
                exact row_14_30
    · by_cases h31_63 : V < 47
      · by_cases h31_47 : V < 39
        · by_cases h31_39 : V < 35
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_14_31
              · have he : V = 32 := by omega
                subst V
                exact row_14_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_14_33
              · have he : V = 34 := by omega
                subst V
                exact row_14_34
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_14_35
              · have he : V = 36 := by omega
                subst V
                exact row_14_36
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_14_37
              · have he : V = 38 := by omega
                subst V
                exact row_14_38
        · by_cases h39_47 : V < 43
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_14_39
              · have he : V = 40 := by omega
                subst V
                exact row_14_40
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_14_41
              · have he : V = 42 := by omega
                subst V
                exact row_14_42
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_14_43
              · have he : V = 44 := by omega
                subst V
                exact row_14_44
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_14_45
              · have he : V = 46 := by omega
                subst V
                exact row_14_46
      · by_cases h47_63 : V < 55
        · by_cases h47_55 : V < 51
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_14_47
              · have he : V = 48 := by omega
                subst V
                exact row_14_48
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_14_49
              · have he : V = 50 := by omega
                subst V
                exact row_14_50
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_14_51
              · have he : V = 52 := by omega
                subst V
                exact row_14_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_14_53
              · have he : V = 54 := by omega
                subst V
                exact row_14_54
        · by_cases h55_63 : V < 59
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_14_55
              · have he : V = 56 := by omega
                subst V
                exact row_14_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_14_57
              · have he : V = 58 := by omega
                subst V
                exact row_14_58
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_14_59
              · have he : V = 60 := by omega
                subst V
                exact row_14_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_14_61
              · have he : V = 62 := by omega
                subst V
                exact row_14_62
  · by_cases h63_126 : V < 94
    · by_cases h63_94 : V < 78
      · by_cases h63_78 : V < 70
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have he : V = 63 := by omega
              subst V
              exact row_14_63
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_14_64
              · have he : V = 65 := by omega
                subst V
                exact row_14_65
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_14_66
              · have he : V = 67 := by omega
                subst V
                exact row_14_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_14_68
              · have he : V = 69 := by omega
                subst V
                exact row_14_69
        · by_cases h70_78 : V < 74
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_14_70
              · have he : V = 71 := by omega
                subst V
                exact row_14_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_14_72
              · have he : V = 73 := by omega
                subst V
                exact row_14_73
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_14_74
              · have he : V = 75 := by omega
                subst V
                exact row_14_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_14_76
              · have he : V = 77 := by omega
                subst V
                exact row_14_77
      · by_cases h78_94 : V < 86
        · by_cases h78_86 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_14_78
              · have he : V = 79 := by omega
                subst V
                exact row_14_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_14_80
              · have he : V = 81 := by omega
                subst V
                exact row_14_81
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_14_82
              · have he : V = 83 := by omega
                subst V
                exact row_14_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_14_84
              · have he : V = 85 := by omega
                subst V
                exact row_14_85
        · by_cases h86_94 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_14_86
              · have he : V = 87 := by omega
                subst V
                exact row_14_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_14_88
              · have he : V = 89 := by omega
                subst V
                exact row_14_89
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_14_90
              · have he : V = 91 := by omega
                subst V
                exact row_14_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_14_92
              · have he : V = 93 := by omega
                subst V
                exact row_14_93
    · by_cases h94_126 : V < 110
      · by_cases h94_110 : V < 102
        · by_cases h94_102 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_14_94
              · have he : V = 95 := by omega
                subst V
                exact row_14_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_14_96
              · have he : V = 97 := by omega
                subst V
                exact row_14_97
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_14_98
              · have he : V = 99 := by omega
                subst V
                exact row_14_99
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_14_100
              · have he : V = 101 := by omega
                subst V
                exact row_14_101
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_14_102
              · have he : V = 103 := by omega
                subst V
                exact row_14_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_14_104
              · have he : V = 105 := by omega
                subst V
                exact row_14_105
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_14_106
              · have he : V = 107 := by omega
                subst V
                exact row_14_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_14_108
              · have he : V = 109 := by omega
                subst V
                exact row_14_109
      · by_cases h110_126 : V < 118
        · by_cases h110_118 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_14_110
              · have he : V = 111 := by omega
                subst V
                exact row_14_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_14_112
              · have he : V = 113 := by omega
                subst V
                exact row_14_113
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_14_114
              · have he : V = 115 := by omega
                subst V
                exact row_14_115
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_14_116
              · have he : V = 117 := by omega
                subst V
                exact row_14_117
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_14_118
              · have he : V = 119 := by omega
                subst V
                exact row_14_119
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_14_120
              · have he : V = 121 := by omega
                subst V
                exact row_14_121
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_14_122
              · have he : V = 123 := by omega
                subst V
                exact row_14_123
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_14_124
              · have he : V = 125 := by omega
                subst V
                exact row_14_125
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
