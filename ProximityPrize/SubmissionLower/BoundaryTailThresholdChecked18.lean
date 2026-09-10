import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked17

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_18_0_0 : CertificateAt 18 0 0 := by decide +kernel
theorem cell_18_0_1 : CertificateAt 18 0 1 := by decide +kernel
theorem cell_18_0_2 : CertificateAt 18 0 2 := by decide +kernel
theorem cell_18_0_3 : CertificateAt 18 0 3 := by decide +kernel
theorem cell_18_0_4 : CertificateAt 18 0 4 := by decide +kernel
theorem cell_18_0_5 : CertificateAt 18 0 5 := by decide +kernel
theorem row_18_0 : ThresholdAt 18 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 0 0 cell_18_0_0
    | exact certificate_sound 18 0 1 cell_18_0_1
    | exact certificate_sound 18 0 2 cell_18_0_2
    | exact certificate_sound 18 0 3 cell_18_0_3
    | exact certificate_sound 18 0 4 cell_18_0_4
    | exact certificate_sound 18 0 5 cell_18_0_5
theorem cell_18_1_0 : CertificateAt 18 1 0 := by decide +kernel
theorem cell_18_1_1 : CertificateAt 18 1 1 := by decide +kernel
theorem cell_18_1_2 : CertificateAt 18 1 2 := by decide +kernel
theorem cell_18_1_3 : CertificateAt 18 1 3 := by decide +kernel
theorem cell_18_1_4 : CertificateAt 18 1 4 := by decide +kernel
theorem cell_18_1_5 : CertificateAt 18 1 5 := by decide +kernel
theorem row_18_1 : ThresholdAt 18 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 1 0 cell_18_1_0
    | exact certificate_sound 18 1 1 cell_18_1_1
    | exact certificate_sound 18 1 2 cell_18_1_2
    | exact certificate_sound 18 1 3 cell_18_1_3
    | exact certificate_sound 18 1 4 cell_18_1_4
    | exact certificate_sound 18 1 5 cell_18_1_5
theorem cell_18_2_0 : CertificateAt 18 2 0 := by decide +kernel
theorem cell_18_2_1 : CertificateAt 18 2 1 := by decide +kernel
theorem cell_18_2_2 : CertificateAt 18 2 2 := by decide +kernel
theorem cell_18_2_3 : CertificateAt 18 2 3 := by decide +kernel
theorem cell_18_2_4 : CertificateAt 18 2 4 := by decide +kernel
theorem cell_18_2_5 : CertificateAt 18 2 5 := by decide +kernel
theorem row_18_2 : ThresholdAt 18 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 2 0 cell_18_2_0
    | exact certificate_sound 18 2 1 cell_18_2_1
    | exact certificate_sound 18 2 2 cell_18_2_2
    | exact certificate_sound 18 2 3 cell_18_2_3
    | exact certificate_sound 18 2 4 cell_18_2_4
    | exact certificate_sound 18 2 5 cell_18_2_5
theorem cell_18_3_0 : CertificateAt 18 3 0 := by decide +kernel
theorem cell_18_3_1 : CertificateAt 18 3 1 := by decide +kernel
theorem cell_18_3_2 : CertificateAt 18 3 2 := by decide +kernel
theorem cell_18_3_3 : CertificateAt 18 3 3 := by decide +kernel
theorem cell_18_3_4 : CertificateAt 18 3 4 := by decide +kernel
theorem cell_18_3_5 : CertificateAt 18 3 5 := by decide +kernel
theorem row_18_3 : ThresholdAt 18 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 3 0 cell_18_3_0
    | exact certificate_sound 18 3 1 cell_18_3_1
    | exact certificate_sound 18 3 2 cell_18_3_2
    | exact certificate_sound 18 3 3 cell_18_3_3
    | exact certificate_sound 18 3 4 cell_18_3_4
    | exact certificate_sound 18 3 5 cell_18_3_5
theorem cell_18_4_0 : CertificateAt 18 4 0 := by decide +kernel
theorem cell_18_4_1 : CertificateAt 18 4 1 := by decide +kernel
theorem cell_18_4_2 : CertificateAt 18 4 2 := by decide +kernel
theorem cell_18_4_3 : CertificateAt 18 4 3 := by decide +kernel
theorem cell_18_4_4 : CertificateAt 18 4 4 := by decide +kernel
theorem cell_18_4_5 : CertificateAt 18 4 5 := by decide +kernel
theorem row_18_4 : ThresholdAt 18 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 4 0 cell_18_4_0
    | exact certificate_sound 18 4 1 cell_18_4_1
    | exact certificate_sound 18 4 2 cell_18_4_2
    | exact certificate_sound 18 4 3 cell_18_4_3
    | exact certificate_sound 18 4 4 cell_18_4_4
    | exact certificate_sound 18 4 5 cell_18_4_5
theorem cell_18_5_0 : CertificateAt 18 5 0 := by decide +kernel
theorem cell_18_5_1 : CertificateAt 18 5 1 := by decide +kernel
theorem cell_18_5_2 : CertificateAt 18 5 2 := by decide +kernel
theorem cell_18_5_3 : CertificateAt 18 5 3 := by decide +kernel
theorem cell_18_5_4 : CertificateAt 18 5 4 := by decide +kernel
theorem cell_18_5_5 : CertificateAt 18 5 5 := by decide +kernel
theorem row_18_5 : ThresholdAt 18 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 5 0 cell_18_5_0
    | exact certificate_sound 18 5 1 cell_18_5_1
    | exact certificate_sound 18 5 2 cell_18_5_2
    | exact certificate_sound 18 5 3 cell_18_5_3
    | exact certificate_sound 18 5 4 cell_18_5_4
    | exact certificate_sound 18 5 5 cell_18_5_5
theorem cell_18_6_0 : CertificateAt 18 6 0 := by decide +kernel
theorem cell_18_6_1 : CertificateAt 18 6 1 := by decide +kernel
theorem cell_18_6_2 : CertificateAt 18 6 2 := by decide +kernel
theorem cell_18_6_3 : CertificateAt 18 6 3 := by decide +kernel
theorem cell_18_6_4 : CertificateAt 18 6 4 := by decide +kernel
theorem cell_18_6_5 : CertificateAt 18 6 5 := by decide +kernel
theorem row_18_6 : ThresholdAt 18 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 6 0 cell_18_6_0
    | exact certificate_sound 18 6 1 cell_18_6_1
    | exact certificate_sound 18 6 2 cell_18_6_2
    | exact certificate_sound 18 6 3 cell_18_6_3
    | exact certificate_sound 18 6 4 cell_18_6_4
    | exact certificate_sound 18 6 5 cell_18_6_5
theorem cell_18_7_0 : CertificateAt 18 7 0 := by decide +kernel
theorem cell_18_7_1 : CertificateAt 18 7 1 := by decide +kernel
theorem cell_18_7_2 : CertificateAt 18 7 2 := by decide +kernel
theorem cell_18_7_3 : CertificateAt 18 7 3 := by decide +kernel
theorem cell_18_7_4 : CertificateAt 18 7 4 := by decide +kernel
theorem cell_18_7_5 : CertificateAt 18 7 5 := by decide +kernel
theorem row_18_7 : ThresholdAt 18 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 7 0 cell_18_7_0
    | exact certificate_sound 18 7 1 cell_18_7_1
    | exact certificate_sound 18 7 2 cell_18_7_2
    | exact certificate_sound 18 7 3 cell_18_7_3
    | exact certificate_sound 18 7 4 cell_18_7_4
    | exact certificate_sound 18 7 5 cell_18_7_5
theorem cell_18_8_0 : CertificateAt 18 8 0 := by decide +kernel
theorem cell_18_8_1 : CertificateAt 18 8 1 := by decide +kernel
theorem cell_18_8_2 : CertificateAt 18 8 2 := by decide +kernel
theorem cell_18_8_3 : CertificateAt 18 8 3 := by decide +kernel
theorem cell_18_8_4 : CertificateAt 18 8 4 := by decide +kernel
theorem cell_18_8_5 : CertificateAt 18 8 5 := by decide +kernel
theorem row_18_8 : ThresholdAt 18 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 8 0 cell_18_8_0
    | exact certificate_sound 18 8 1 cell_18_8_1
    | exact certificate_sound 18 8 2 cell_18_8_2
    | exact certificate_sound 18 8 3 cell_18_8_3
    | exact certificate_sound 18 8 4 cell_18_8_4
    | exact certificate_sound 18 8 5 cell_18_8_5
theorem cell_18_9_0 : CertificateAt 18 9 0 := by decide +kernel
theorem cell_18_9_1 : CertificateAt 18 9 1 := by decide +kernel
theorem cell_18_9_2 : CertificateAt 18 9 2 := by decide +kernel
theorem cell_18_9_3 : CertificateAt 18 9 3 := by decide +kernel
theorem cell_18_9_4 : CertificateAt 18 9 4 := by decide +kernel
theorem cell_18_9_5 : CertificateAt 18 9 5 := by decide +kernel
theorem row_18_9 : ThresholdAt 18 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 9 0 cell_18_9_0
    | exact certificate_sound 18 9 1 cell_18_9_1
    | exact certificate_sound 18 9 2 cell_18_9_2
    | exact certificate_sound 18 9 3 cell_18_9_3
    | exact certificate_sound 18 9 4 cell_18_9_4
    | exact certificate_sound 18 9 5 cell_18_9_5
theorem cell_18_10_0 : CertificateAt 18 10 0 := by decide +kernel
theorem cell_18_10_1 : CertificateAt 18 10 1 := by decide +kernel
theorem cell_18_10_2 : CertificateAt 18 10 2 := by decide +kernel
theorem cell_18_10_3 : CertificateAt 18 10 3 := by decide +kernel
theorem cell_18_10_4 : CertificateAt 18 10 4 := by decide +kernel
theorem cell_18_10_5 : CertificateAt 18 10 5 := by decide +kernel
theorem row_18_10 : ThresholdAt 18 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 10 0 cell_18_10_0
    | exact certificate_sound 18 10 1 cell_18_10_1
    | exact certificate_sound 18 10 2 cell_18_10_2
    | exact certificate_sound 18 10 3 cell_18_10_3
    | exact certificate_sound 18 10 4 cell_18_10_4
    | exact certificate_sound 18 10 5 cell_18_10_5
theorem cell_18_11_0 : CertificateAt 18 11 0 := by decide +kernel
theorem cell_18_11_1 : CertificateAt 18 11 1 := by decide +kernel
theorem cell_18_11_2 : CertificateAt 18 11 2 := by decide +kernel
theorem cell_18_11_3 : CertificateAt 18 11 3 := by decide +kernel
theorem cell_18_11_4 : CertificateAt 18 11 4 := by decide +kernel
theorem cell_18_11_5 : CertificateAt 18 11 5 := by decide +kernel
theorem row_18_11 : ThresholdAt 18 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 11 0 cell_18_11_0
    | exact certificate_sound 18 11 1 cell_18_11_1
    | exact certificate_sound 18 11 2 cell_18_11_2
    | exact certificate_sound 18 11 3 cell_18_11_3
    | exact certificate_sound 18 11 4 cell_18_11_4
    | exact certificate_sound 18 11 5 cell_18_11_5
theorem cell_18_12_0 : CertificateAt 18 12 0 := by decide +kernel
theorem cell_18_12_1 : CertificateAt 18 12 1 := by decide +kernel
theorem cell_18_12_2 : CertificateAt 18 12 2 := by decide +kernel
theorem cell_18_12_3 : CertificateAt 18 12 3 := by decide +kernel
theorem cell_18_12_4 : CertificateAt 18 12 4 := by decide +kernel
theorem cell_18_12_5 : CertificateAt 18 12 5 := by decide +kernel
theorem row_18_12 : ThresholdAt 18 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 12 0 cell_18_12_0
    | exact certificate_sound 18 12 1 cell_18_12_1
    | exact certificate_sound 18 12 2 cell_18_12_2
    | exact certificate_sound 18 12 3 cell_18_12_3
    | exact certificate_sound 18 12 4 cell_18_12_4
    | exact certificate_sound 18 12 5 cell_18_12_5
theorem cell_18_13_0 : CertificateAt 18 13 0 := by decide +kernel
theorem cell_18_13_1 : CertificateAt 18 13 1 := by decide +kernel
theorem cell_18_13_2 : CertificateAt 18 13 2 := by decide +kernel
theorem cell_18_13_3 : CertificateAt 18 13 3 := by decide +kernel
theorem cell_18_13_4 : CertificateAt 18 13 4 := by decide +kernel
theorem cell_18_13_5 : CertificateAt 18 13 5 := by decide +kernel
theorem row_18_13 : ThresholdAt 18 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 13 0 cell_18_13_0
    | exact certificate_sound 18 13 1 cell_18_13_1
    | exact certificate_sound 18 13 2 cell_18_13_2
    | exact certificate_sound 18 13 3 cell_18_13_3
    | exact certificate_sound 18 13 4 cell_18_13_4
    | exact certificate_sound 18 13 5 cell_18_13_5
theorem cell_18_14_0 : CertificateAt 18 14 0 := by decide +kernel
theorem cell_18_14_1 : CertificateAt 18 14 1 := by decide +kernel
theorem cell_18_14_2 : CertificateAt 18 14 2 := by decide +kernel
theorem cell_18_14_3 : CertificateAt 18 14 3 := by decide +kernel
theorem cell_18_14_4 : CertificateAt 18 14 4 := by decide +kernel
theorem cell_18_14_5 : CertificateAt 18 14 5 := by decide +kernel
theorem row_18_14 : ThresholdAt 18 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 14 0 cell_18_14_0
    | exact certificate_sound 18 14 1 cell_18_14_1
    | exact certificate_sound 18 14 2 cell_18_14_2
    | exact certificate_sound 18 14 3 cell_18_14_3
    | exact certificate_sound 18 14 4 cell_18_14_4
    | exact certificate_sound 18 14 5 cell_18_14_5
theorem cell_18_15_0 : CertificateAt 18 15 0 := by decide +kernel
theorem cell_18_15_1 : CertificateAt 18 15 1 := by decide +kernel
theorem cell_18_15_2 : CertificateAt 18 15 2 := by decide +kernel
theorem cell_18_15_3 : CertificateAt 18 15 3 := by decide +kernel
theorem cell_18_15_4 : CertificateAt 18 15 4 := by decide +kernel
theorem cell_18_15_5 : CertificateAt 18 15 5 := by decide +kernel
theorem row_18_15 : ThresholdAt 18 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 15 0 cell_18_15_0
    | exact certificate_sound 18 15 1 cell_18_15_1
    | exact certificate_sound 18 15 2 cell_18_15_2
    | exact certificate_sound 18 15 3 cell_18_15_3
    | exact certificate_sound 18 15 4 cell_18_15_4
    | exact certificate_sound 18 15 5 cell_18_15_5
theorem cell_18_16_0 : CertificateAt 18 16 0 := by decide +kernel
theorem cell_18_16_1 : CertificateAt 18 16 1 := by decide +kernel
theorem cell_18_16_2 : CertificateAt 18 16 2 := by decide +kernel
theorem cell_18_16_3 : CertificateAt 18 16 3 := by decide +kernel
theorem cell_18_16_4 : CertificateAt 18 16 4 := by decide +kernel
theorem cell_18_16_5 : CertificateAt 18 16 5 := by decide +kernel
theorem row_18_16 : ThresholdAt 18 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 16 0 cell_18_16_0
    | exact certificate_sound 18 16 1 cell_18_16_1
    | exact certificate_sound 18 16 2 cell_18_16_2
    | exact certificate_sound 18 16 3 cell_18_16_3
    | exact certificate_sound 18 16 4 cell_18_16_4
    | exact certificate_sound 18 16 5 cell_18_16_5
theorem cell_18_17_0 : CertificateAt 18 17 0 := by decide +kernel
theorem cell_18_17_1 : CertificateAt 18 17 1 := by decide +kernel
theorem cell_18_17_2 : CertificateAt 18 17 2 := by decide +kernel
theorem cell_18_17_3 : CertificateAt 18 17 3 := by decide +kernel
theorem cell_18_17_4 : CertificateAt 18 17 4 := by decide +kernel
theorem cell_18_17_5 : CertificateAt 18 17 5 := by decide +kernel
theorem row_18_17 : ThresholdAt 18 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 17 0 cell_18_17_0
    | exact certificate_sound 18 17 1 cell_18_17_1
    | exact certificate_sound 18 17 2 cell_18_17_2
    | exact certificate_sound 18 17 3 cell_18_17_3
    | exact certificate_sound 18 17 4 cell_18_17_4
    | exact certificate_sound 18 17 5 cell_18_17_5
theorem cell_18_18_0 : CertificateAt 18 18 0 := by decide +kernel
theorem cell_18_18_1 : CertificateAt 18 18 1 := by decide +kernel
theorem cell_18_18_2 : CertificateAt 18 18 2 := by decide +kernel
theorem cell_18_18_3 : CertificateAt 18 18 3 := by decide +kernel
theorem cell_18_18_4 : CertificateAt 18 18 4 := by decide +kernel
theorem cell_18_18_5 : CertificateAt 18 18 5 := by decide +kernel
theorem row_18_18 : ThresholdAt 18 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 18 0 cell_18_18_0
    | exact certificate_sound 18 18 1 cell_18_18_1
    | exact certificate_sound 18 18 2 cell_18_18_2
    | exact certificate_sound 18 18 3 cell_18_18_3
    | exact certificate_sound 18 18 4 cell_18_18_4
    | exact certificate_sound 18 18 5 cell_18_18_5
theorem cell_18_19_0 : CertificateAt 18 19 0 := by decide +kernel
theorem cell_18_19_1 : CertificateAt 18 19 1 := by decide +kernel
theorem cell_18_19_2 : CertificateAt 18 19 2 := by decide +kernel
theorem cell_18_19_3 : CertificateAt 18 19 3 := by decide +kernel
theorem cell_18_19_4 : CertificateAt 18 19 4 := by decide +kernel
theorem cell_18_19_5 : CertificateAt 18 19 5 := by decide +kernel
theorem row_18_19 : ThresholdAt 18 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 19 0 cell_18_19_0
    | exact certificate_sound 18 19 1 cell_18_19_1
    | exact certificate_sound 18 19 2 cell_18_19_2
    | exact certificate_sound 18 19 3 cell_18_19_3
    | exact certificate_sound 18 19 4 cell_18_19_4
    | exact certificate_sound 18 19 5 cell_18_19_5
theorem cell_18_20_0 : CertificateAt 18 20 0 := by decide +kernel
theorem cell_18_20_1 : CertificateAt 18 20 1 := by decide +kernel
theorem cell_18_20_2 : CertificateAt 18 20 2 := by decide +kernel
theorem cell_18_20_3 : CertificateAt 18 20 3 := by decide +kernel
theorem cell_18_20_4 : CertificateAt 18 20 4 := by decide +kernel
theorem cell_18_20_5 : CertificateAt 18 20 5 := by decide +kernel
theorem row_18_20 : ThresholdAt 18 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 20 0 cell_18_20_0
    | exact certificate_sound 18 20 1 cell_18_20_1
    | exact certificate_sound 18 20 2 cell_18_20_2
    | exact certificate_sound 18 20 3 cell_18_20_3
    | exact certificate_sound 18 20 4 cell_18_20_4
    | exact certificate_sound 18 20 5 cell_18_20_5
theorem cell_18_21_0 : CertificateAt 18 21 0 := by decide +kernel
theorem cell_18_21_1 : CertificateAt 18 21 1 := by decide +kernel
theorem cell_18_21_2 : CertificateAt 18 21 2 := by decide +kernel
theorem cell_18_21_3 : CertificateAt 18 21 3 := by decide +kernel
theorem cell_18_21_4 : CertificateAt 18 21 4 := by decide +kernel
theorem cell_18_21_5 : CertificateAt 18 21 5 := by decide +kernel
theorem row_18_21 : ThresholdAt 18 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 21 0 cell_18_21_0
    | exact certificate_sound 18 21 1 cell_18_21_1
    | exact certificate_sound 18 21 2 cell_18_21_2
    | exact certificate_sound 18 21 3 cell_18_21_3
    | exact certificate_sound 18 21 4 cell_18_21_4
    | exact certificate_sound 18 21 5 cell_18_21_5
theorem cell_18_22_0 : CertificateAt 18 22 0 := by decide +kernel
theorem cell_18_22_1 : CertificateAt 18 22 1 := by decide +kernel
theorem cell_18_22_2 : CertificateAt 18 22 2 := by decide +kernel
theorem cell_18_22_3 : CertificateAt 18 22 3 := by decide +kernel
theorem cell_18_22_4 : CertificateAt 18 22 4 := by decide +kernel
theorem cell_18_22_5 : CertificateAt 18 22 5 := by decide +kernel
theorem row_18_22 : ThresholdAt 18 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 22 0 cell_18_22_0
    | exact certificate_sound 18 22 1 cell_18_22_1
    | exact certificate_sound 18 22 2 cell_18_22_2
    | exact certificate_sound 18 22 3 cell_18_22_3
    | exact certificate_sound 18 22 4 cell_18_22_4
    | exact certificate_sound 18 22 5 cell_18_22_5
theorem cell_18_23_0 : CertificateAt 18 23 0 := by decide +kernel
theorem cell_18_23_1 : CertificateAt 18 23 1 := by decide +kernel
theorem cell_18_23_2 : CertificateAt 18 23 2 := by decide +kernel
theorem cell_18_23_3 : CertificateAt 18 23 3 := by decide +kernel
theorem cell_18_23_4 : CertificateAt 18 23 4 := by decide +kernel
theorem cell_18_23_5 : CertificateAt 18 23 5 := by decide +kernel
theorem row_18_23 : ThresholdAt 18 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 23 0 cell_18_23_0
    | exact certificate_sound 18 23 1 cell_18_23_1
    | exact certificate_sound 18 23 2 cell_18_23_2
    | exact certificate_sound 18 23 3 cell_18_23_3
    | exact certificate_sound 18 23 4 cell_18_23_4
    | exact certificate_sound 18 23 5 cell_18_23_5
theorem cell_18_24_0 : CertificateAt 18 24 0 := by decide +kernel
theorem cell_18_24_1 : CertificateAt 18 24 1 := by decide +kernel
theorem cell_18_24_2 : CertificateAt 18 24 2 := by decide +kernel
theorem cell_18_24_3 : CertificateAt 18 24 3 := by decide +kernel
theorem cell_18_24_4 : CertificateAt 18 24 4 := by decide +kernel
theorem cell_18_24_5 : CertificateAt 18 24 5 := by decide +kernel
theorem row_18_24 : ThresholdAt 18 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 24 0 cell_18_24_0
    | exact certificate_sound 18 24 1 cell_18_24_1
    | exact certificate_sound 18 24 2 cell_18_24_2
    | exact certificate_sound 18 24 3 cell_18_24_3
    | exact certificate_sound 18 24 4 cell_18_24_4
    | exact certificate_sound 18 24 5 cell_18_24_5
theorem cell_18_25_0 : CertificateAt 18 25 0 := by decide +kernel
theorem cell_18_25_1 : CertificateAt 18 25 1 := by decide +kernel
theorem cell_18_25_2 : CertificateAt 18 25 2 := by decide +kernel
theorem cell_18_25_3 : CertificateAt 18 25 3 := by decide +kernel
theorem cell_18_25_4 : CertificateAt 18 25 4 := by decide +kernel
theorem cell_18_25_5 : CertificateAt 18 25 5 := by decide +kernel
theorem row_18_25 : ThresholdAt 18 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 25 0 cell_18_25_0
    | exact certificate_sound 18 25 1 cell_18_25_1
    | exact certificate_sound 18 25 2 cell_18_25_2
    | exact certificate_sound 18 25 3 cell_18_25_3
    | exact certificate_sound 18 25 4 cell_18_25_4
    | exact certificate_sound 18 25 5 cell_18_25_5
theorem cell_18_26_0 : CertificateAt 18 26 0 := by decide +kernel
theorem cell_18_26_1 : CertificateAt 18 26 1 := by decide +kernel
theorem cell_18_26_2 : CertificateAt 18 26 2 := by decide +kernel
theorem cell_18_26_3 : CertificateAt 18 26 3 := by decide +kernel
theorem cell_18_26_4 : CertificateAt 18 26 4 := by decide +kernel
theorem cell_18_26_5 : CertificateAt 18 26 5 := by decide +kernel
theorem row_18_26 : ThresholdAt 18 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 26 0 cell_18_26_0
    | exact certificate_sound 18 26 1 cell_18_26_1
    | exact certificate_sound 18 26 2 cell_18_26_2
    | exact certificate_sound 18 26 3 cell_18_26_3
    | exact certificate_sound 18 26 4 cell_18_26_4
    | exact certificate_sound 18 26 5 cell_18_26_5
theorem cell_18_27_0 : CertificateAt 18 27 0 := by decide +kernel
theorem cell_18_27_1 : CertificateAt 18 27 1 := by decide +kernel
theorem cell_18_27_2 : CertificateAt 18 27 2 := by decide +kernel
theorem cell_18_27_3 : CertificateAt 18 27 3 := by decide +kernel
theorem cell_18_27_4 : CertificateAt 18 27 4 := by decide +kernel
theorem cell_18_27_5 : CertificateAt 18 27 5 := by decide +kernel
theorem row_18_27 : ThresholdAt 18 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 27 0 cell_18_27_0
    | exact certificate_sound 18 27 1 cell_18_27_1
    | exact certificate_sound 18 27 2 cell_18_27_2
    | exact certificate_sound 18 27 3 cell_18_27_3
    | exact certificate_sound 18 27 4 cell_18_27_4
    | exact certificate_sound 18 27 5 cell_18_27_5
theorem cell_18_28_0 : CertificateAt 18 28 0 := by decide +kernel
theorem cell_18_28_1 : CertificateAt 18 28 1 := by decide +kernel
theorem cell_18_28_2 : CertificateAt 18 28 2 := by decide +kernel
theorem cell_18_28_3 : CertificateAt 18 28 3 := by decide +kernel
theorem cell_18_28_4 : CertificateAt 18 28 4 := by decide +kernel
theorem cell_18_28_5 : CertificateAt 18 28 5 := by decide +kernel
theorem row_18_28 : ThresholdAt 18 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 28 0 cell_18_28_0
    | exact certificate_sound 18 28 1 cell_18_28_1
    | exact certificate_sound 18 28 2 cell_18_28_2
    | exact certificate_sound 18 28 3 cell_18_28_3
    | exact certificate_sound 18 28 4 cell_18_28_4
    | exact certificate_sound 18 28 5 cell_18_28_5
theorem cell_18_29_0 : CertificateAt 18 29 0 := by decide +kernel
theorem cell_18_29_1 : CertificateAt 18 29 1 := by decide +kernel
theorem cell_18_29_2 : CertificateAt 18 29 2 := by decide +kernel
theorem cell_18_29_3 : CertificateAt 18 29 3 := by decide +kernel
theorem cell_18_29_4 : CertificateAt 18 29 4 := by decide +kernel
theorem cell_18_29_5 : CertificateAt 18 29 5 := by decide +kernel
theorem row_18_29 : ThresholdAt 18 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 29 0 cell_18_29_0
    | exact certificate_sound 18 29 1 cell_18_29_1
    | exact certificate_sound 18 29 2 cell_18_29_2
    | exact certificate_sound 18 29 3 cell_18_29_3
    | exact certificate_sound 18 29 4 cell_18_29_4
    | exact certificate_sound 18 29 5 cell_18_29_5
theorem cell_18_30_0 : CertificateAt 18 30 0 := by decide +kernel
theorem cell_18_30_1 : CertificateAt 18 30 1 := by decide +kernel
theorem cell_18_30_2 : CertificateAt 18 30 2 := by decide +kernel
theorem cell_18_30_3 : CertificateAt 18 30 3 := by decide +kernel
theorem cell_18_30_4 : CertificateAt 18 30 4 := by decide +kernel
theorem cell_18_30_5 : CertificateAt 18 30 5 := by decide +kernel
theorem row_18_30 : ThresholdAt 18 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 30 0 cell_18_30_0
    | exact certificate_sound 18 30 1 cell_18_30_1
    | exact certificate_sound 18 30 2 cell_18_30_2
    | exact certificate_sound 18 30 3 cell_18_30_3
    | exact certificate_sound 18 30 4 cell_18_30_4
    | exact certificate_sound 18 30 5 cell_18_30_5
theorem cell_18_31_0 : CertificateAt 18 31 0 := by decide +kernel
theorem cell_18_31_1 : CertificateAt 18 31 1 := by decide +kernel
theorem cell_18_31_2 : CertificateAt 18 31 2 := by decide +kernel
theorem cell_18_31_3 : CertificateAt 18 31 3 := by decide +kernel
theorem cell_18_31_4 : CertificateAt 18 31 4 := by decide +kernel
theorem cell_18_31_5 : CertificateAt 18 31 5 := by decide +kernel
theorem row_18_31 : ThresholdAt 18 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 31 0 cell_18_31_0
    | exact certificate_sound 18 31 1 cell_18_31_1
    | exact certificate_sound 18 31 2 cell_18_31_2
    | exact certificate_sound 18 31 3 cell_18_31_3
    | exact certificate_sound 18 31 4 cell_18_31_4
    | exact certificate_sound 18 31 5 cell_18_31_5
theorem cell_18_32_0 : CertificateAt 18 32 0 := by decide +kernel
theorem cell_18_32_1 : CertificateAt 18 32 1 := by decide +kernel
theorem cell_18_32_2 : CertificateAt 18 32 2 := by decide +kernel
theorem cell_18_32_3 : CertificateAt 18 32 3 := by decide +kernel
theorem cell_18_32_4 : CertificateAt 18 32 4 := by decide +kernel
theorem cell_18_32_5 : CertificateAt 18 32 5 := by decide +kernel
theorem row_18_32 : ThresholdAt 18 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 32 0 cell_18_32_0
    | exact certificate_sound 18 32 1 cell_18_32_1
    | exact certificate_sound 18 32 2 cell_18_32_2
    | exact certificate_sound 18 32 3 cell_18_32_3
    | exact certificate_sound 18 32 4 cell_18_32_4
    | exact certificate_sound 18 32 5 cell_18_32_5
theorem cell_18_33_0 : CertificateAt 18 33 0 := by decide +kernel
theorem cell_18_33_1 : CertificateAt 18 33 1 := by decide +kernel
theorem cell_18_33_2 : CertificateAt 18 33 2 := by decide +kernel
theorem cell_18_33_3 : CertificateAt 18 33 3 := by decide +kernel
theorem cell_18_33_4 : CertificateAt 18 33 4 := by decide +kernel
theorem cell_18_33_5 : CertificateAt 18 33 5 := by decide +kernel
theorem row_18_33 : ThresholdAt 18 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 33 0 cell_18_33_0
    | exact certificate_sound 18 33 1 cell_18_33_1
    | exact certificate_sound 18 33 2 cell_18_33_2
    | exact certificate_sound 18 33 3 cell_18_33_3
    | exact certificate_sound 18 33 4 cell_18_33_4
    | exact certificate_sound 18 33 5 cell_18_33_5
theorem cell_18_34_0 : CertificateAt 18 34 0 := by decide +kernel
theorem cell_18_34_1 : CertificateAt 18 34 1 := by decide +kernel
theorem cell_18_34_2 : CertificateAt 18 34 2 := by decide +kernel
theorem cell_18_34_3 : CertificateAt 18 34 3 := by decide +kernel
theorem cell_18_34_4 : CertificateAt 18 34 4 := by decide +kernel
theorem cell_18_34_5 : CertificateAt 18 34 5 := by decide +kernel
theorem row_18_34 : ThresholdAt 18 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 34 0 cell_18_34_0
    | exact certificate_sound 18 34 1 cell_18_34_1
    | exact certificate_sound 18 34 2 cell_18_34_2
    | exact certificate_sound 18 34 3 cell_18_34_3
    | exact certificate_sound 18 34 4 cell_18_34_4
    | exact certificate_sound 18 34 5 cell_18_34_5
theorem cell_18_35_0 : CertificateAt 18 35 0 := by decide +kernel
theorem cell_18_35_1 : CertificateAt 18 35 1 := by decide +kernel
theorem cell_18_35_2 : CertificateAt 18 35 2 := by decide +kernel
theorem cell_18_35_3 : CertificateAt 18 35 3 := by decide +kernel
theorem cell_18_35_4 : CertificateAt 18 35 4 := by decide +kernel
theorem cell_18_35_5 : CertificateAt 18 35 5 := by decide +kernel
theorem row_18_35 : ThresholdAt 18 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 35 0 cell_18_35_0
    | exact certificate_sound 18 35 1 cell_18_35_1
    | exact certificate_sound 18 35 2 cell_18_35_2
    | exact certificate_sound 18 35 3 cell_18_35_3
    | exact certificate_sound 18 35 4 cell_18_35_4
    | exact certificate_sound 18 35 5 cell_18_35_5
theorem cell_18_36_0 : CertificateAt 18 36 0 := by decide +kernel
theorem cell_18_36_1 : CertificateAt 18 36 1 := by decide +kernel
theorem cell_18_36_2 : CertificateAt 18 36 2 := by decide +kernel
theorem cell_18_36_3 : CertificateAt 18 36 3 := by decide +kernel
theorem cell_18_36_4 : CertificateAt 18 36 4 := by decide +kernel
theorem cell_18_36_5 : CertificateAt 18 36 5 := by decide +kernel
theorem row_18_36 : ThresholdAt 18 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 36 0 cell_18_36_0
    | exact certificate_sound 18 36 1 cell_18_36_1
    | exact certificate_sound 18 36 2 cell_18_36_2
    | exact certificate_sound 18 36 3 cell_18_36_3
    | exact certificate_sound 18 36 4 cell_18_36_4
    | exact certificate_sound 18 36 5 cell_18_36_5
theorem cell_18_37_0 : CertificateAt 18 37 0 := by decide +kernel
theorem cell_18_37_1 : CertificateAt 18 37 1 := by decide +kernel
theorem cell_18_37_2 : CertificateAt 18 37 2 := by decide +kernel
theorem cell_18_37_3 : CertificateAt 18 37 3 := by decide +kernel
theorem cell_18_37_4 : CertificateAt 18 37 4 := by decide +kernel
theorem cell_18_37_5 : CertificateAt 18 37 5 := by decide +kernel
theorem row_18_37 : ThresholdAt 18 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 37 0 cell_18_37_0
    | exact certificate_sound 18 37 1 cell_18_37_1
    | exact certificate_sound 18 37 2 cell_18_37_2
    | exact certificate_sound 18 37 3 cell_18_37_3
    | exact certificate_sound 18 37 4 cell_18_37_4
    | exact certificate_sound 18 37 5 cell_18_37_5
theorem cell_18_38_0 : CertificateAt 18 38 0 := by decide +kernel
theorem cell_18_38_1 : CertificateAt 18 38 1 := by decide +kernel
theorem cell_18_38_2 : CertificateAt 18 38 2 := by decide +kernel
theorem cell_18_38_3 : CertificateAt 18 38 3 := by decide +kernel
theorem cell_18_38_4 : CertificateAt 18 38 4 := by decide +kernel
theorem cell_18_38_5 : CertificateAt 18 38 5 := by decide +kernel
theorem row_18_38 : ThresholdAt 18 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 38 0 cell_18_38_0
    | exact certificate_sound 18 38 1 cell_18_38_1
    | exact certificate_sound 18 38 2 cell_18_38_2
    | exact certificate_sound 18 38 3 cell_18_38_3
    | exact certificate_sound 18 38 4 cell_18_38_4
    | exact certificate_sound 18 38 5 cell_18_38_5
theorem cell_18_39_0 : CertificateAt 18 39 0 := by decide +kernel
theorem cell_18_39_1 : CertificateAt 18 39 1 := by decide +kernel
theorem cell_18_39_2 : CertificateAt 18 39 2 := by decide +kernel
theorem cell_18_39_3 : CertificateAt 18 39 3 := by decide +kernel
theorem cell_18_39_4 : CertificateAt 18 39 4 := by decide +kernel
theorem cell_18_39_5 : CertificateAt 18 39 5 := by decide +kernel
theorem row_18_39 : ThresholdAt 18 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 39 0 cell_18_39_0
    | exact certificate_sound 18 39 1 cell_18_39_1
    | exact certificate_sound 18 39 2 cell_18_39_2
    | exact certificate_sound 18 39 3 cell_18_39_3
    | exact certificate_sound 18 39 4 cell_18_39_4
    | exact certificate_sound 18 39 5 cell_18_39_5
theorem cell_18_40_0 : CertificateAt 18 40 0 := by decide +kernel
theorem cell_18_40_1 : CertificateAt 18 40 1 := by decide +kernel
theorem cell_18_40_2 : CertificateAt 18 40 2 := by decide +kernel
theorem cell_18_40_3 : CertificateAt 18 40 3 := by decide +kernel
theorem cell_18_40_4 : CertificateAt 18 40 4 := by decide +kernel
theorem cell_18_40_5 : CertificateAt 18 40 5 := by decide +kernel
theorem row_18_40 : ThresholdAt 18 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 40 0 cell_18_40_0
    | exact certificate_sound 18 40 1 cell_18_40_1
    | exact certificate_sound 18 40 2 cell_18_40_2
    | exact certificate_sound 18 40 3 cell_18_40_3
    | exact certificate_sound 18 40 4 cell_18_40_4
    | exact certificate_sound 18 40 5 cell_18_40_5
theorem cell_18_41_0 : CertificateAt 18 41 0 := by decide +kernel
theorem cell_18_41_1 : CertificateAt 18 41 1 := by decide +kernel
theorem cell_18_41_2 : CertificateAt 18 41 2 := by decide +kernel
theorem cell_18_41_3 : CertificateAt 18 41 3 := by decide +kernel
theorem cell_18_41_4 : CertificateAt 18 41 4 := by decide +kernel
theorem cell_18_41_5 : CertificateAt 18 41 5 := by decide +kernel
theorem row_18_41 : ThresholdAt 18 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 41 0 cell_18_41_0
    | exact certificate_sound 18 41 1 cell_18_41_1
    | exact certificate_sound 18 41 2 cell_18_41_2
    | exact certificate_sound 18 41 3 cell_18_41_3
    | exact certificate_sound 18 41 4 cell_18_41_4
    | exact certificate_sound 18 41 5 cell_18_41_5
theorem cell_18_42_0 : CertificateAt 18 42 0 := by decide +kernel
theorem cell_18_42_1 : CertificateAt 18 42 1 := by decide +kernel
theorem cell_18_42_2 : CertificateAt 18 42 2 := by decide +kernel
theorem cell_18_42_3 : CertificateAt 18 42 3 := by decide +kernel
theorem cell_18_42_4 : CertificateAt 18 42 4 := by decide +kernel
theorem cell_18_42_5 : CertificateAt 18 42 5 := by decide +kernel
theorem row_18_42 : ThresholdAt 18 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 42 0 cell_18_42_0
    | exact certificate_sound 18 42 1 cell_18_42_1
    | exact certificate_sound 18 42 2 cell_18_42_2
    | exact certificate_sound 18 42 3 cell_18_42_3
    | exact certificate_sound 18 42 4 cell_18_42_4
    | exact certificate_sound 18 42 5 cell_18_42_5
theorem cell_18_43_0 : CertificateAt 18 43 0 := by decide +kernel
theorem cell_18_43_1 : CertificateAt 18 43 1 := by decide +kernel
theorem cell_18_43_2 : CertificateAt 18 43 2 := by decide +kernel
theorem cell_18_43_3 : CertificateAt 18 43 3 := by decide +kernel
theorem cell_18_43_4 : CertificateAt 18 43 4 := by decide +kernel
theorem cell_18_43_5 : CertificateAt 18 43 5 := by decide +kernel
theorem row_18_43 : ThresholdAt 18 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 43 0 cell_18_43_0
    | exact certificate_sound 18 43 1 cell_18_43_1
    | exact certificate_sound 18 43 2 cell_18_43_2
    | exact certificate_sound 18 43 3 cell_18_43_3
    | exact certificate_sound 18 43 4 cell_18_43_4
    | exact certificate_sound 18 43 5 cell_18_43_5
theorem cell_18_44_0 : CertificateAt 18 44 0 := by decide +kernel
theorem cell_18_44_1 : CertificateAt 18 44 1 := by decide +kernel
theorem cell_18_44_2 : CertificateAt 18 44 2 := by decide +kernel
theorem cell_18_44_3 : CertificateAt 18 44 3 := by decide +kernel
theorem cell_18_44_4 : CertificateAt 18 44 4 := by decide +kernel
theorem cell_18_44_5 : CertificateAt 18 44 5 := by decide +kernel
theorem row_18_44 : ThresholdAt 18 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 44 0 cell_18_44_0
    | exact certificate_sound 18 44 1 cell_18_44_1
    | exact certificate_sound 18 44 2 cell_18_44_2
    | exact certificate_sound 18 44 3 cell_18_44_3
    | exact certificate_sound 18 44 4 cell_18_44_4
    | exact certificate_sound 18 44 5 cell_18_44_5
theorem cell_18_45_0 : CertificateAt 18 45 0 := by decide +kernel
theorem cell_18_45_1 : CertificateAt 18 45 1 := by decide +kernel
theorem cell_18_45_2 : CertificateAt 18 45 2 := by decide +kernel
theorem cell_18_45_3 : CertificateAt 18 45 3 := by decide +kernel
theorem cell_18_45_4 : CertificateAt 18 45 4 := by decide +kernel
theorem cell_18_45_5 : CertificateAt 18 45 5 := by decide +kernel
theorem row_18_45 : ThresholdAt 18 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 45 0 cell_18_45_0
    | exact certificate_sound 18 45 1 cell_18_45_1
    | exact certificate_sound 18 45 2 cell_18_45_2
    | exact certificate_sound 18 45 3 cell_18_45_3
    | exact certificate_sound 18 45 4 cell_18_45_4
    | exact certificate_sound 18 45 5 cell_18_45_5
theorem cell_18_46_0 : CertificateAt 18 46 0 := by decide +kernel
theorem cell_18_46_1 : CertificateAt 18 46 1 := by decide +kernel
theorem cell_18_46_2 : CertificateAt 18 46 2 := by decide +kernel
theorem cell_18_46_3 : CertificateAt 18 46 3 := by decide +kernel
theorem cell_18_46_4 : CertificateAt 18 46 4 := by decide +kernel
theorem cell_18_46_5 : CertificateAt 18 46 5 := by decide +kernel
theorem row_18_46 : ThresholdAt 18 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 46 0 cell_18_46_0
    | exact certificate_sound 18 46 1 cell_18_46_1
    | exact certificate_sound 18 46 2 cell_18_46_2
    | exact certificate_sound 18 46 3 cell_18_46_3
    | exact certificate_sound 18 46 4 cell_18_46_4
    | exact certificate_sound 18 46 5 cell_18_46_5
theorem cell_18_47_0 : CertificateAt 18 47 0 := by decide +kernel
theorem cell_18_47_1 : CertificateAt 18 47 1 := by decide +kernel
theorem cell_18_47_2 : CertificateAt 18 47 2 := by decide +kernel
theorem cell_18_47_3 : CertificateAt 18 47 3 := by decide +kernel
theorem cell_18_47_4 : CertificateAt 18 47 4 := by decide +kernel
theorem cell_18_47_5 : CertificateAt 18 47 5 := by decide +kernel
theorem row_18_47 : ThresholdAt 18 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 47 0 cell_18_47_0
    | exact certificate_sound 18 47 1 cell_18_47_1
    | exact certificate_sound 18 47 2 cell_18_47_2
    | exact certificate_sound 18 47 3 cell_18_47_3
    | exact certificate_sound 18 47 4 cell_18_47_4
    | exact certificate_sound 18 47 5 cell_18_47_5
theorem cell_18_48_0 : CertificateAt 18 48 0 := by decide +kernel
theorem cell_18_48_1 : CertificateAt 18 48 1 := by decide +kernel
theorem cell_18_48_2 : CertificateAt 18 48 2 := by decide +kernel
theorem cell_18_48_3 : CertificateAt 18 48 3 := by decide +kernel
theorem cell_18_48_4 : CertificateAt 18 48 4 := by decide +kernel
theorem cell_18_48_5 : CertificateAt 18 48 5 := by decide +kernel
theorem row_18_48 : ThresholdAt 18 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 48 0 cell_18_48_0
    | exact certificate_sound 18 48 1 cell_18_48_1
    | exact certificate_sound 18 48 2 cell_18_48_2
    | exact certificate_sound 18 48 3 cell_18_48_3
    | exact certificate_sound 18 48 4 cell_18_48_4
    | exact certificate_sound 18 48 5 cell_18_48_5
theorem cell_18_49_0 : CertificateAt 18 49 0 := by decide +kernel
theorem cell_18_49_1 : CertificateAt 18 49 1 := by decide +kernel
theorem cell_18_49_2 : CertificateAt 18 49 2 := by decide +kernel
theorem cell_18_49_3 : CertificateAt 18 49 3 := by decide +kernel
theorem cell_18_49_4 : CertificateAt 18 49 4 := by decide +kernel
theorem cell_18_49_5 : CertificateAt 18 49 5 := by decide +kernel
theorem row_18_49 : ThresholdAt 18 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 49 0 cell_18_49_0
    | exact certificate_sound 18 49 1 cell_18_49_1
    | exact certificate_sound 18 49 2 cell_18_49_2
    | exact certificate_sound 18 49 3 cell_18_49_3
    | exact certificate_sound 18 49 4 cell_18_49_4
    | exact certificate_sound 18 49 5 cell_18_49_5
theorem cell_18_50_0 : CertificateAt 18 50 0 := by decide +kernel
theorem cell_18_50_1 : CertificateAt 18 50 1 := by decide +kernel
theorem cell_18_50_2 : CertificateAt 18 50 2 := by decide +kernel
theorem cell_18_50_3 : CertificateAt 18 50 3 := by decide +kernel
theorem cell_18_50_4 : CertificateAt 18 50 4 := by decide +kernel
theorem cell_18_50_5 : CertificateAt 18 50 5 := by decide +kernel
theorem row_18_50 : ThresholdAt 18 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 50 0 cell_18_50_0
    | exact certificate_sound 18 50 1 cell_18_50_1
    | exact certificate_sound 18 50 2 cell_18_50_2
    | exact certificate_sound 18 50 3 cell_18_50_3
    | exact certificate_sound 18 50 4 cell_18_50_4
    | exact certificate_sound 18 50 5 cell_18_50_5
theorem cell_18_51_0 : CertificateAt 18 51 0 := by decide +kernel
theorem cell_18_51_1 : CertificateAt 18 51 1 := by decide +kernel
theorem cell_18_51_2 : CertificateAt 18 51 2 := by decide +kernel
theorem cell_18_51_3 : CertificateAt 18 51 3 := by decide +kernel
theorem cell_18_51_4 : CertificateAt 18 51 4 := by decide +kernel
theorem cell_18_51_5 : CertificateAt 18 51 5 := by decide +kernel
theorem row_18_51 : ThresholdAt 18 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 51 0 cell_18_51_0
    | exact certificate_sound 18 51 1 cell_18_51_1
    | exact certificate_sound 18 51 2 cell_18_51_2
    | exact certificate_sound 18 51 3 cell_18_51_3
    | exact certificate_sound 18 51 4 cell_18_51_4
    | exact certificate_sound 18 51 5 cell_18_51_5
theorem cell_18_52_0 : CertificateAt 18 52 0 := by decide +kernel
theorem cell_18_52_1 : CertificateAt 18 52 1 := by decide +kernel
theorem cell_18_52_2 : CertificateAt 18 52 2 := by decide +kernel
theorem cell_18_52_3 : CertificateAt 18 52 3 := by decide +kernel
theorem cell_18_52_4 : CertificateAt 18 52 4 := by decide +kernel
theorem cell_18_52_5 : CertificateAt 18 52 5 := by decide +kernel
theorem row_18_52 : ThresholdAt 18 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 52 0 cell_18_52_0
    | exact certificate_sound 18 52 1 cell_18_52_1
    | exact certificate_sound 18 52 2 cell_18_52_2
    | exact certificate_sound 18 52 3 cell_18_52_3
    | exact certificate_sound 18 52 4 cell_18_52_4
    | exact certificate_sound 18 52 5 cell_18_52_5
theorem cell_18_53_0 : CertificateAt 18 53 0 := by decide +kernel
theorem cell_18_53_1 : CertificateAt 18 53 1 := by decide +kernel
theorem cell_18_53_2 : CertificateAt 18 53 2 := by decide +kernel
theorem cell_18_53_3 : CertificateAt 18 53 3 := by decide +kernel
theorem cell_18_53_4 : CertificateAt 18 53 4 := by decide +kernel
theorem cell_18_53_5 : CertificateAt 18 53 5 := by decide +kernel
theorem row_18_53 : ThresholdAt 18 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 53 0 cell_18_53_0
    | exact certificate_sound 18 53 1 cell_18_53_1
    | exact certificate_sound 18 53 2 cell_18_53_2
    | exact certificate_sound 18 53 3 cell_18_53_3
    | exact certificate_sound 18 53 4 cell_18_53_4
    | exact certificate_sound 18 53 5 cell_18_53_5
theorem cell_18_54_0 : CertificateAt 18 54 0 := by decide +kernel
theorem cell_18_54_1 : CertificateAt 18 54 1 := by decide +kernel
theorem cell_18_54_2 : CertificateAt 18 54 2 := by decide +kernel
theorem cell_18_54_3 : CertificateAt 18 54 3 := by decide +kernel
theorem cell_18_54_4 : CertificateAt 18 54 4 := by decide +kernel
theorem cell_18_54_5 : CertificateAt 18 54 5 := by decide +kernel
theorem row_18_54 : ThresholdAt 18 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 54 0 cell_18_54_0
    | exact certificate_sound 18 54 1 cell_18_54_1
    | exact certificate_sound 18 54 2 cell_18_54_2
    | exact certificate_sound 18 54 3 cell_18_54_3
    | exact certificate_sound 18 54 4 cell_18_54_4
    | exact certificate_sound 18 54 5 cell_18_54_5
theorem cell_18_55_0 : CertificateAt 18 55 0 := by decide +kernel
theorem cell_18_55_1 : CertificateAt 18 55 1 := by decide +kernel
theorem cell_18_55_2 : CertificateAt 18 55 2 := by decide +kernel
theorem cell_18_55_3 : CertificateAt 18 55 3 := by decide +kernel
theorem cell_18_55_4 : CertificateAt 18 55 4 := by decide +kernel
theorem cell_18_55_5 : CertificateAt 18 55 5 := by decide +kernel
theorem row_18_55 : ThresholdAt 18 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 55 0 cell_18_55_0
    | exact certificate_sound 18 55 1 cell_18_55_1
    | exact certificate_sound 18 55 2 cell_18_55_2
    | exact certificate_sound 18 55 3 cell_18_55_3
    | exact certificate_sound 18 55 4 cell_18_55_4
    | exact certificate_sound 18 55 5 cell_18_55_5
theorem cell_18_56_0 : CertificateAt 18 56 0 := by decide +kernel
theorem cell_18_56_1 : CertificateAt 18 56 1 := by decide +kernel
theorem cell_18_56_2 : CertificateAt 18 56 2 := by decide +kernel
theorem cell_18_56_3 : CertificateAt 18 56 3 := by decide +kernel
theorem cell_18_56_4 : CertificateAt 18 56 4 := by decide +kernel
theorem cell_18_56_5 : CertificateAt 18 56 5 := by decide +kernel
theorem row_18_56 : ThresholdAt 18 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 56 0 cell_18_56_0
    | exact certificate_sound 18 56 1 cell_18_56_1
    | exact certificate_sound 18 56 2 cell_18_56_2
    | exact certificate_sound 18 56 3 cell_18_56_3
    | exact certificate_sound 18 56 4 cell_18_56_4
    | exact certificate_sound 18 56 5 cell_18_56_5
theorem cell_18_57_0 : CertificateAt 18 57 0 := by decide +kernel
theorem cell_18_57_1 : CertificateAt 18 57 1 := by decide +kernel
theorem cell_18_57_2 : CertificateAt 18 57 2 := by decide +kernel
theorem cell_18_57_3 : CertificateAt 18 57 3 := by decide +kernel
theorem cell_18_57_4 : CertificateAt 18 57 4 := by decide +kernel
theorem cell_18_57_5 : CertificateAt 18 57 5 := by decide +kernel
theorem row_18_57 : ThresholdAt 18 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 57 0 cell_18_57_0
    | exact certificate_sound 18 57 1 cell_18_57_1
    | exact certificate_sound 18 57 2 cell_18_57_2
    | exact certificate_sound 18 57 3 cell_18_57_3
    | exact certificate_sound 18 57 4 cell_18_57_4
    | exact certificate_sound 18 57 5 cell_18_57_5
theorem cell_18_58_0 : CertificateAt 18 58 0 := by decide +kernel
theorem cell_18_58_1 : CertificateAt 18 58 1 := by decide +kernel
theorem cell_18_58_2 : CertificateAt 18 58 2 := by decide +kernel
theorem cell_18_58_3 : CertificateAt 18 58 3 := by decide +kernel
theorem cell_18_58_4 : CertificateAt 18 58 4 := by decide +kernel
theorem cell_18_58_5 : CertificateAt 18 58 5 := by decide +kernel
theorem row_18_58 : ThresholdAt 18 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 58 0 cell_18_58_0
    | exact certificate_sound 18 58 1 cell_18_58_1
    | exact certificate_sound 18 58 2 cell_18_58_2
    | exact certificate_sound 18 58 3 cell_18_58_3
    | exact certificate_sound 18 58 4 cell_18_58_4
    | exact certificate_sound 18 58 5 cell_18_58_5
theorem cell_18_59_0 : CertificateAt 18 59 0 := by decide +kernel
theorem cell_18_59_1 : CertificateAt 18 59 1 := by decide +kernel
theorem cell_18_59_2 : CertificateAt 18 59 2 := by decide +kernel
theorem cell_18_59_3 : CertificateAt 18 59 3 := by decide +kernel
theorem cell_18_59_4 : CertificateAt 18 59 4 := by decide +kernel
theorem cell_18_59_5 : CertificateAt 18 59 5 := by decide +kernel
theorem row_18_59 : ThresholdAt 18 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 59 0 cell_18_59_0
    | exact certificate_sound 18 59 1 cell_18_59_1
    | exact certificate_sound 18 59 2 cell_18_59_2
    | exact certificate_sound 18 59 3 cell_18_59_3
    | exact certificate_sound 18 59 4 cell_18_59_4
    | exact certificate_sound 18 59 5 cell_18_59_5
theorem cell_18_60_0 : CertificateAt 18 60 0 := by decide +kernel
theorem cell_18_60_1 : CertificateAt 18 60 1 := by decide +kernel
theorem cell_18_60_2 : CertificateAt 18 60 2 := by decide +kernel
theorem cell_18_60_3 : CertificateAt 18 60 3 := by decide +kernel
theorem cell_18_60_4 : CertificateAt 18 60 4 := by decide +kernel
theorem cell_18_60_5 : CertificateAt 18 60 5 := by decide +kernel
theorem row_18_60 : ThresholdAt 18 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 60 0 cell_18_60_0
    | exact certificate_sound 18 60 1 cell_18_60_1
    | exact certificate_sound 18 60 2 cell_18_60_2
    | exact certificate_sound 18 60 3 cell_18_60_3
    | exact certificate_sound 18 60 4 cell_18_60_4
    | exact certificate_sound 18 60 5 cell_18_60_5
theorem cell_18_61_0 : CertificateAt 18 61 0 := by decide +kernel
theorem cell_18_61_1 : CertificateAt 18 61 1 := by decide +kernel
theorem cell_18_61_2 : CertificateAt 18 61 2 := by decide +kernel
theorem cell_18_61_3 : CertificateAt 18 61 3 := by decide +kernel
theorem cell_18_61_4 : CertificateAt 18 61 4 := by decide +kernel
theorem cell_18_61_5 : CertificateAt 18 61 5 := by decide +kernel
theorem row_18_61 : ThresholdAt 18 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 61 0 cell_18_61_0
    | exact certificate_sound 18 61 1 cell_18_61_1
    | exact certificate_sound 18 61 2 cell_18_61_2
    | exact certificate_sound 18 61 3 cell_18_61_3
    | exact certificate_sound 18 61 4 cell_18_61_4
    | exact certificate_sound 18 61 5 cell_18_61_5
theorem cell_18_62_0 : CertificateAt 18 62 0 := by decide +kernel
theorem cell_18_62_1 : CertificateAt 18 62 1 := by decide +kernel
theorem cell_18_62_2 : CertificateAt 18 62 2 := by decide +kernel
theorem cell_18_62_3 : CertificateAt 18 62 3 := by decide +kernel
theorem cell_18_62_4 : CertificateAt 18 62 4 := by decide +kernel
theorem cell_18_62_5 : CertificateAt 18 62 5 := by decide +kernel
theorem row_18_62 : ThresholdAt 18 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 62 0 cell_18_62_0
    | exact certificate_sound 18 62 1 cell_18_62_1
    | exact certificate_sound 18 62 2 cell_18_62_2
    | exact certificate_sound 18 62 3 cell_18_62_3
    | exact certificate_sound 18 62 4 cell_18_62_4
    | exact certificate_sound 18 62 5 cell_18_62_5
theorem cell_18_63_0 : CertificateAt 18 63 0 := by decide +kernel
theorem cell_18_63_1 : CertificateAt 18 63 1 := by decide +kernel
theorem cell_18_63_2 : CertificateAt 18 63 2 := by decide +kernel
theorem cell_18_63_3 : CertificateAt 18 63 3 := by decide +kernel
theorem cell_18_63_4 : CertificateAt 18 63 4 := by decide +kernel
theorem cell_18_63_5 : CertificateAt 18 63 5 := by decide +kernel
theorem row_18_63 : ThresholdAt 18 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 63 0 cell_18_63_0
    | exact certificate_sound 18 63 1 cell_18_63_1
    | exact certificate_sound 18 63 2 cell_18_63_2
    | exact certificate_sound 18 63 3 cell_18_63_3
    | exact certificate_sound 18 63 4 cell_18_63_4
    | exact certificate_sound 18 63 5 cell_18_63_5
theorem cell_18_64_0 : CertificateAt 18 64 0 := by decide +kernel
theorem cell_18_64_1 : CertificateAt 18 64 1 := by decide +kernel
theorem cell_18_64_2 : CertificateAt 18 64 2 := by decide +kernel
theorem cell_18_64_3 : CertificateAt 18 64 3 := by decide +kernel
theorem cell_18_64_4 : CertificateAt 18 64 4 := by decide +kernel
theorem cell_18_64_5 : CertificateAt 18 64 5 := by decide +kernel
theorem row_18_64 : ThresholdAt 18 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 64 0 cell_18_64_0
    | exact certificate_sound 18 64 1 cell_18_64_1
    | exact certificate_sound 18 64 2 cell_18_64_2
    | exact certificate_sound 18 64 3 cell_18_64_3
    | exact certificate_sound 18 64 4 cell_18_64_4
    | exact certificate_sound 18 64 5 cell_18_64_5
theorem cell_18_65_0 : CertificateAt 18 65 0 := by decide +kernel
theorem cell_18_65_1 : CertificateAt 18 65 1 := by decide +kernel
theorem cell_18_65_2 : CertificateAt 18 65 2 := by decide +kernel
theorem cell_18_65_3 : CertificateAt 18 65 3 := by decide +kernel
theorem cell_18_65_4 : CertificateAt 18 65 4 := by decide +kernel
theorem cell_18_65_5 : CertificateAt 18 65 5 := by decide +kernel
theorem row_18_65 : ThresholdAt 18 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 65 0 cell_18_65_0
    | exact certificate_sound 18 65 1 cell_18_65_1
    | exact certificate_sound 18 65 2 cell_18_65_2
    | exact certificate_sound 18 65 3 cell_18_65_3
    | exact certificate_sound 18 65 4 cell_18_65_4
    | exact certificate_sound 18 65 5 cell_18_65_5
theorem cell_18_66_0 : CertificateAt 18 66 0 := by decide +kernel
theorem cell_18_66_1 : CertificateAt 18 66 1 := by decide +kernel
theorem cell_18_66_2 : CertificateAt 18 66 2 := by decide +kernel
theorem cell_18_66_3 : CertificateAt 18 66 3 := by decide +kernel
theorem cell_18_66_4 : CertificateAt 18 66 4 := by decide +kernel
theorem cell_18_66_5 : CertificateAt 18 66 5 := by decide +kernel
theorem row_18_66 : ThresholdAt 18 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 66 0 cell_18_66_0
    | exact certificate_sound 18 66 1 cell_18_66_1
    | exact certificate_sound 18 66 2 cell_18_66_2
    | exact certificate_sound 18 66 3 cell_18_66_3
    | exact certificate_sound 18 66 4 cell_18_66_4
    | exact certificate_sound 18 66 5 cell_18_66_5
theorem cell_18_67_0 : CertificateAt 18 67 0 := by decide +kernel
theorem cell_18_67_1 : CertificateAt 18 67 1 := by decide +kernel
theorem cell_18_67_2 : CertificateAt 18 67 2 := by decide +kernel
theorem cell_18_67_3 : CertificateAt 18 67 3 := by decide +kernel
theorem cell_18_67_4 : CertificateAt 18 67 4 := by decide +kernel
theorem cell_18_67_5 : CertificateAt 18 67 5 := by decide +kernel
theorem row_18_67 : ThresholdAt 18 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 67 0 cell_18_67_0
    | exact certificate_sound 18 67 1 cell_18_67_1
    | exact certificate_sound 18 67 2 cell_18_67_2
    | exact certificate_sound 18 67 3 cell_18_67_3
    | exact certificate_sound 18 67 4 cell_18_67_4
    | exact certificate_sound 18 67 5 cell_18_67_5
theorem cell_18_68_0 : CertificateAt 18 68 0 := by decide +kernel
theorem cell_18_68_1 : CertificateAt 18 68 1 := by decide +kernel
theorem cell_18_68_2 : CertificateAt 18 68 2 := by decide +kernel
theorem cell_18_68_3 : CertificateAt 18 68 3 := by decide +kernel
theorem cell_18_68_4 : CertificateAt 18 68 4 := by decide +kernel
theorem cell_18_68_5 : CertificateAt 18 68 5 := by decide +kernel
theorem row_18_68 : ThresholdAt 18 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 68 0 cell_18_68_0
    | exact certificate_sound 18 68 1 cell_18_68_1
    | exact certificate_sound 18 68 2 cell_18_68_2
    | exact certificate_sound 18 68 3 cell_18_68_3
    | exact certificate_sound 18 68 4 cell_18_68_4
    | exact certificate_sound 18 68 5 cell_18_68_5
theorem cell_18_69_0 : CertificateAt 18 69 0 := by decide +kernel
theorem cell_18_69_1 : CertificateAt 18 69 1 := by decide +kernel
theorem cell_18_69_2 : CertificateAt 18 69 2 := by decide +kernel
theorem cell_18_69_3 : CertificateAt 18 69 3 := by decide +kernel
theorem cell_18_69_4 : CertificateAt 18 69 4 := by decide +kernel
theorem cell_18_69_5 : CertificateAt 18 69 5 := by decide +kernel
theorem row_18_69 : ThresholdAt 18 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 69 0 cell_18_69_0
    | exact certificate_sound 18 69 1 cell_18_69_1
    | exact certificate_sound 18 69 2 cell_18_69_2
    | exact certificate_sound 18 69 3 cell_18_69_3
    | exact certificate_sound 18 69 4 cell_18_69_4
    | exact certificate_sound 18 69 5 cell_18_69_5
theorem cell_18_70_0 : CertificateAt 18 70 0 := by decide +kernel
theorem cell_18_70_1 : CertificateAt 18 70 1 := by decide +kernel
theorem cell_18_70_2 : CertificateAt 18 70 2 := by decide +kernel
theorem cell_18_70_3 : CertificateAt 18 70 3 := by decide +kernel
theorem cell_18_70_4 : CertificateAt 18 70 4 := by decide +kernel
theorem cell_18_70_5 : CertificateAt 18 70 5 := by decide +kernel
theorem row_18_70 : ThresholdAt 18 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 70 0 cell_18_70_0
    | exact certificate_sound 18 70 1 cell_18_70_1
    | exact certificate_sound 18 70 2 cell_18_70_2
    | exact certificate_sound 18 70 3 cell_18_70_3
    | exact certificate_sound 18 70 4 cell_18_70_4
    | exact certificate_sound 18 70 5 cell_18_70_5
theorem cell_18_71_0 : CertificateAt 18 71 0 := by decide +kernel
theorem cell_18_71_1 : CertificateAt 18 71 1 := by decide +kernel
theorem cell_18_71_2 : CertificateAt 18 71 2 := by decide +kernel
theorem cell_18_71_3 : CertificateAt 18 71 3 := by decide +kernel
theorem cell_18_71_4 : CertificateAt 18 71 4 := by decide +kernel
theorem cell_18_71_5 : CertificateAt 18 71 5 := by decide +kernel
theorem row_18_71 : ThresholdAt 18 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 71 0 cell_18_71_0
    | exact certificate_sound 18 71 1 cell_18_71_1
    | exact certificate_sound 18 71 2 cell_18_71_2
    | exact certificate_sound 18 71 3 cell_18_71_3
    | exact certificate_sound 18 71 4 cell_18_71_4
    | exact certificate_sound 18 71 5 cell_18_71_5
theorem cell_18_72_0 : CertificateAt 18 72 0 := by decide +kernel
theorem cell_18_72_1 : CertificateAt 18 72 1 := by decide +kernel
theorem cell_18_72_2 : CertificateAt 18 72 2 := by decide +kernel
theorem cell_18_72_3 : CertificateAt 18 72 3 := by decide +kernel
theorem cell_18_72_4 : CertificateAt 18 72 4 := by decide +kernel
theorem cell_18_72_5 : CertificateAt 18 72 5 := by decide +kernel
theorem row_18_72 : ThresholdAt 18 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 72 0 cell_18_72_0
    | exact certificate_sound 18 72 1 cell_18_72_1
    | exact certificate_sound 18 72 2 cell_18_72_2
    | exact certificate_sound 18 72 3 cell_18_72_3
    | exact certificate_sound 18 72 4 cell_18_72_4
    | exact certificate_sound 18 72 5 cell_18_72_5
theorem cell_18_73_0 : CertificateAt 18 73 0 := by decide +kernel
theorem cell_18_73_1 : CertificateAt 18 73 1 := by decide +kernel
theorem cell_18_73_2 : CertificateAt 18 73 2 := by decide +kernel
theorem cell_18_73_3 : CertificateAt 18 73 3 := by decide +kernel
theorem cell_18_73_4 : CertificateAt 18 73 4 := by decide +kernel
theorem cell_18_73_5 : CertificateAt 18 73 5 := by decide +kernel
theorem row_18_73 : ThresholdAt 18 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 73 0 cell_18_73_0
    | exact certificate_sound 18 73 1 cell_18_73_1
    | exact certificate_sound 18 73 2 cell_18_73_2
    | exact certificate_sound 18 73 3 cell_18_73_3
    | exact certificate_sound 18 73 4 cell_18_73_4
    | exact certificate_sound 18 73 5 cell_18_73_5
theorem cell_18_74_0 : CertificateAt 18 74 0 := by decide +kernel
theorem cell_18_74_1 : CertificateAt 18 74 1 := by decide +kernel
theorem cell_18_74_2 : CertificateAt 18 74 2 := by decide +kernel
theorem cell_18_74_3 : CertificateAt 18 74 3 := by decide +kernel
theorem cell_18_74_4 : CertificateAt 18 74 4 := by decide +kernel
theorem cell_18_74_5 : CertificateAt 18 74 5 := by decide +kernel
theorem row_18_74 : ThresholdAt 18 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 74 0 cell_18_74_0
    | exact certificate_sound 18 74 1 cell_18_74_1
    | exact certificate_sound 18 74 2 cell_18_74_2
    | exact certificate_sound 18 74 3 cell_18_74_3
    | exact certificate_sound 18 74 4 cell_18_74_4
    | exact certificate_sound 18 74 5 cell_18_74_5
theorem cell_18_75_0 : CertificateAt 18 75 0 := by decide +kernel
theorem cell_18_75_1 : CertificateAt 18 75 1 := by decide +kernel
theorem cell_18_75_2 : CertificateAt 18 75 2 := by decide +kernel
theorem cell_18_75_3 : CertificateAt 18 75 3 := by decide +kernel
theorem cell_18_75_4 : CertificateAt 18 75 4 := by decide +kernel
theorem cell_18_75_5 : CertificateAt 18 75 5 := by decide +kernel
theorem row_18_75 : ThresholdAt 18 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 75 0 cell_18_75_0
    | exact certificate_sound 18 75 1 cell_18_75_1
    | exact certificate_sound 18 75 2 cell_18_75_2
    | exact certificate_sound 18 75 3 cell_18_75_3
    | exact certificate_sound 18 75 4 cell_18_75_4
    | exact certificate_sound 18 75 5 cell_18_75_5
theorem cell_18_76_0 : CertificateAt 18 76 0 := by decide +kernel
theorem cell_18_76_1 : CertificateAt 18 76 1 := by decide +kernel
theorem cell_18_76_2 : CertificateAt 18 76 2 := by decide +kernel
theorem cell_18_76_3 : CertificateAt 18 76 3 := by decide +kernel
theorem cell_18_76_4 : CertificateAt 18 76 4 := by decide +kernel
theorem cell_18_76_5 : CertificateAt 18 76 5 := by decide +kernel
theorem row_18_76 : ThresholdAt 18 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 76 0 cell_18_76_0
    | exact certificate_sound 18 76 1 cell_18_76_1
    | exact certificate_sound 18 76 2 cell_18_76_2
    | exact certificate_sound 18 76 3 cell_18_76_3
    | exact certificate_sound 18 76 4 cell_18_76_4
    | exact certificate_sound 18 76 5 cell_18_76_5
theorem cell_18_77_0 : CertificateAt 18 77 0 := by decide +kernel
theorem cell_18_77_1 : CertificateAt 18 77 1 := by decide +kernel
theorem cell_18_77_2 : CertificateAt 18 77 2 := by decide +kernel
theorem cell_18_77_3 : CertificateAt 18 77 3 := by decide +kernel
theorem cell_18_77_4 : CertificateAt 18 77 4 := by decide +kernel
theorem cell_18_77_5 : CertificateAt 18 77 5 := by decide +kernel
theorem row_18_77 : ThresholdAt 18 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 77 0 cell_18_77_0
    | exact certificate_sound 18 77 1 cell_18_77_1
    | exact certificate_sound 18 77 2 cell_18_77_2
    | exact certificate_sound 18 77 3 cell_18_77_3
    | exact certificate_sound 18 77 4 cell_18_77_4
    | exact certificate_sound 18 77 5 cell_18_77_5
theorem cell_18_78_0 : CertificateAt 18 78 0 := by decide +kernel
theorem cell_18_78_1 : CertificateAt 18 78 1 := by decide +kernel
theorem cell_18_78_2 : CertificateAt 18 78 2 := by decide +kernel
theorem cell_18_78_3 : CertificateAt 18 78 3 := by decide +kernel
theorem cell_18_78_4 : CertificateAt 18 78 4 := by decide +kernel
theorem cell_18_78_5 : CertificateAt 18 78 5 := by decide +kernel
theorem row_18_78 : ThresholdAt 18 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 78 0 cell_18_78_0
    | exact certificate_sound 18 78 1 cell_18_78_1
    | exact certificate_sound 18 78 2 cell_18_78_2
    | exact certificate_sound 18 78 3 cell_18_78_3
    | exact certificate_sound 18 78 4 cell_18_78_4
    | exact certificate_sound 18 78 5 cell_18_78_5
theorem cell_18_79_0 : CertificateAt 18 79 0 := by decide +kernel
theorem cell_18_79_1 : CertificateAt 18 79 1 := by decide +kernel
theorem cell_18_79_2 : CertificateAt 18 79 2 := by decide +kernel
theorem cell_18_79_3 : CertificateAt 18 79 3 := by decide +kernel
theorem cell_18_79_4 : CertificateAt 18 79 4 := by decide +kernel
theorem cell_18_79_5 : CertificateAt 18 79 5 := by decide +kernel
theorem row_18_79 : ThresholdAt 18 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 79 0 cell_18_79_0
    | exact certificate_sound 18 79 1 cell_18_79_1
    | exact certificate_sound 18 79 2 cell_18_79_2
    | exact certificate_sound 18 79 3 cell_18_79_3
    | exact certificate_sound 18 79 4 cell_18_79_4
    | exact certificate_sound 18 79 5 cell_18_79_5
theorem cell_18_80_0 : CertificateAt 18 80 0 := by decide +kernel
theorem cell_18_80_1 : CertificateAt 18 80 1 := by decide +kernel
theorem cell_18_80_2 : CertificateAt 18 80 2 := by decide +kernel
theorem cell_18_80_3 : CertificateAt 18 80 3 := by decide +kernel
theorem cell_18_80_4 : CertificateAt 18 80 4 := by decide +kernel
theorem cell_18_80_5 : CertificateAt 18 80 5 := by decide +kernel
theorem row_18_80 : ThresholdAt 18 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 80 0 cell_18_80_0
    | exact certificate_sound 18 80 1 cell_18_80_1
    | exact certificate_sound 18 80 2 cell_18_80_2
    | exact certificate_sound 18 80 3 cell_18_80_3
    | exact certificate_sound 18 80 4 cell_18_80_4
    | exact certificate_sound 18 80 5 cell_18_80_5
theorem cell_18_81_0 : CertificateAt 18 81 0 := by decide +kernel
theorem cell_18_81_1 : CertificateAt 18 81 1 := by decide +kernel
theorem cell_18_81_2 : CertificateAt 18 81 2 := by decide +kernel
theorem cell_18_81_3 : CertificateAt 18 81 3 := by decide +kernel
theorem cell_18_81_4 : CertificateAt 18 81 4 := by decide +kernel
theorem cell_18_81_5 : CertificateAt 18 81 5 := by decide +kernel
theorem row_18_81 : ThresholdAt 18 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 81 0 cell_18_81_0
    | exact certificate_sound 18 81 1 cell_18_81_1
    | exact certificate_sound 18 81 2 cell_18_81_2
    | exact certificate_sound 18 81 3 cell_18_81_3
    | exact certificate_sound 18 81 4 cell_18_81_4
    | exact certificate_sound 18 81 5 cell_18_81_5
theorem cell_18_82_0 : CertificateAt 18 82 0 := by decide +kernel
theorem cell_18_82_1 : CertificateAt 18 82 1 := by decide +kernel
theorem cell_18_82_2 : CertificateAt 18 82 2 := by decide +kernel
theorem cell_18_82_3 : CertificateAt 18 82 3 := by decide +kernel
theorem cell_18_82_4 : CertificateAt 18 82 4 := by decide +kernel
theorem cell_18_82_5 : CertificateAt 18 82 5 := by decide +kernel
theorem row_18_82 : ThresholdAt 18 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 82 0 cell_18_82_0
    | exact certificate_sound 18 82 1 cell_18_82_1
    | exact certificate_sound 18 82 2 cell_18_82_2
    | exact certificate_sound 18 82 3 cell_18_82_3
    | exact certificate_sound 18 82 4 cell_18_82_4
    | exact certificate_sound 18 82 5 cell_18_82_5
theorem cell_18_83_0 : CertificateAt 18 83 0 := by decide +kernel
theorem cell_18_83_1 : CertificateAt 18 83 1 := by decide +kernel
theorem cell_18_83_2 : CertificateAt 18 83 2 := by decide +kernel
theorem cell_18_83_3 : CertificateAt 18 83 3 := by decide +kernel
theorem cell_18_83_4 : CertificateAt 18 83 4 := by decide +kernel
theorem cell_18_83_5 : CertificateAt 18 83 5 := by decide +kernel
theorem row_18_83 : ThresholdAt 18 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 83 0 cell_18_83_0
    | exact certificate_sound 18 83 1 cell_18_83_1
    | exact certificate_sound 18 83 2 cell_18_83_2
    | exact certificate_sound 18 83 3 cell_18_83_3
    | exact certificate_sound 18 83 4 cell_18_83_4
    | exact certificate_sound 18 83 5 cell_18_83_5
theorem cell_18_84_0 : CertificateAt 18 84 0 := by decide +kernel
theorem cell_18_84_1 : CertificateAt 18 84 1 := by decide +kernel
theorem cell_18_84_2 : CertificateAt 18 84 2 := by decide +kernel
theorem cell_18_84_3 : CertificateAt 18 84 3 := by decide +kernel
theorem cell_18_84_4 : CertificateAt 18 84 4 := by decide +kernel
theorem cell_18_84_5 : CertificateAt 18 84 5 := by decide +kernel
theorem row_18_84 : ThresholdAt 18 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 84 0 cell_18_84_0
    | exact certificate_sound 18 84 1 cell_18_84_1
    | exact certificate_sound 18 84 2 cell_18_84_2
    | exact certificate_sound 18 84 3 cell_18_84_3
    | exact certificate_sound 18 84 4 cell_18_84_4
    | exact certificate_sound 18 84 5 cell_18_84_5
theorem cell_18_85_0 : CertificateAt 18 85 0 := by decide +kernel
theorem cell_18_85_1 : CertificateAt 18 85 1 := by decide +kernel
theorem cell_18_85_2 : CertificateAt 18 85 2 := by decide +kernel
theorem cell_18_85_3 : CertificateAt 18 85 3 := by decide +kernel
theorem cell_18_85_4 : CertificateAt 18 85 4 := by decide +kernel
theorem cell_18_85_5 : CertificateAt 18 85 5 := by decide +kernel
theorem row_18_85 : ThresholdAt 18 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 85 0 cell_18_85_0
    | exact certificate_sound 18 85 1 cell_18_85_1
    | exact certificate_sound 18 85 2 cell_18_85_2
    | exact certificate_sound 18 85 3 cell_18_85_3
    | exact certificate_sound 18 85 4 cell_18_85_4
    | exact certificate_sound 18 85 5 cell_18_85_5
theorem cell_18_86_0 : CertificateAt 18 86 0 := by decide +kernel
theorem cell_18_86_1 : CertificateAt 18 86 1 := by decide +kernel
theorem cell_18_86_2 : CertificateAt 18 86 2 := by decide +kernel
theorem cell_18_86_3 : CertificateAt 18 86 3 := by decide +kernel
theorem cell_18_86_4 : CertificateAt 18 86 4 := by decide +kernel
theorem cell_18_86_5 : CertificateAt 18 86 5 := by decide +kernel
theorem row_18_86 : ThresholdAt 18 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 86 0 cell_18_86_0
    | exact certificate_sound 18 86 1 cell_18_86_1
    | exact certificate_sound 18 86 2 cell_18_86_2
    | exact certificate_sound 18 86 3 cell_18_86_3
    | exact certificate_sound 18 86 4 cell_18_86_4
    | exact certificate_sound 18 86 5 cell_18_86_5
theorem cell_18_87_0 : CertificateAt 18 87 0 := by decide +kernel
theorem cell_18_87_1 : CertificateAt 18 87 1 := by decide +kernel
theorem cell_18_87_2 : CertificateAt 18 87 2 := by decide +kernel
theorem cell_18_87_3 : CertificateAt 18 87 3 := by decide +kernel
theorem cell_18_87_4 : CertificateAt 18 87 4 := by decide +kernel
theorem cell_18_87_5 : CertificateAt 18 87 5 := by decide +kernel
theorem row_18_87 : ThresholdAt 18 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 87 0 cell_18_87_0
    | exact certificate_sound 18 87 1 cell_18_87_1
    | exact certificate_sound 18 87 2 cell_18_87_2
    | exact certificate_sound 18 87 3 cell_18_87_3
    | exact certificate_sound 18 87 4 cell_18_87_4
    | exact certificate_sound 18 87 5 cell_18_87_5
theorem cell_18_88_0 : CertificateAt 18 88 0 := by decide +kernel
theorem cell_18_88_1 : CertificateAt 18 88 1 := by decide +kernel
theorem cell_18_88_2 : CertificateAt 18 88 2 := by decide +kernel
theorem cell_18_88_3 : CertificateAt 18 88 3 := by decide +kernel
theorem cell_18_88_4 : CertificateAt 18 88 4 := by decide +kernel
theorem cell_18_88_5 : CertificateAt 18 88 5 := by decide +kernel
theorem row_18_88 : ThresholdAt 18 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 88 0 cell_18_88_0
    | exact certificate_sound 18 88 1 cell_18_88_1
    | exact certificate_sound 18 88 2 cell_18_88_2
    | exact certificate_sound 18 88 3 cell_18_88_3
    | exact certificate_sound 18 88 4 cell_18_88_4
    | exact certificate_sound 18 88 5 cell_18_88_5
theorem cell_18_89_0 : CertificateAt 18 89 0 := by decide +kernel
theorem cell_18_89_1 : CertificateAt 18 89 1 := by decide +kernel
theorem cell_18_89_2 : CertificateAt 18 89 2 := by decide +kernel
theorem cell_18_89_3 : CertificateAt 18 89 3 := by decide +kernel
theorem cell_18_89_4 : CertificateAt 18 89 4 := by decide +kernel
theorem cell_18_89_5 : CertificateAt 18 89 5 := by decide +kernel
theorem row_18_89 : ThresholdAt 18 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 89 0 cell_18_89_0
    | exact certificate_sound 18 89 1 cell_18_89_1
    | exact certificate_sound 18 89 2 cell_18_89_2
    | exact certificate_sound 18 89 3 cell_18_89_3
    | exact certificate_sound 18 89 4 cell_18_89_4
    | exact certificate_sound 18 89 5 cell_18_89_5
theorem cell_18_90_0 : CertificateAt 18 90 0 := by decide +kernel
theorem cell_18_90_1 : CertificateAt 18 90 1 := by decide +kernel
theorem cell_18_90_2 : CertificateAt 18 90 2 := by decide +kernel
theorem cell_18_90_3 : CertificateAt 18 90 3 := by decide +kernel
theorem cell_18_90_4 : CertificateAt 18 90 4 := by decide +kernel
theorem cell_18_90_5 : CertificateAt 18 90 5 := by decide +kernel
theorem row_18_90 : ThresholdAt 18 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 90 0 cell_18_90_0
    | exact certificate_sound 18 90 1 cell_18_90_1
    | exact certificate_sound 18 90 2 cell_18_90_2
    | exact certificate_sound 18 90 3 cell_18_90_3
    | exact certificate_sound 18 90 4 cell_18_90_4
    | exact certificate_sound 18 90 5 cell_18_90_5
theorem cell_18_91_0 : CertificateAt 18 91 0 := by decide +kernel
theorem cell_18_91_1 : CertificateAt 18 91 1 := by decide +kernel
theorem cell_18_91_2 : CertificateAt 18 91 2 := by decide +kernel
theorem cell_18_91_3 : CertificateAt 18 91 3 := by decide +kernel
theorem cell_18_91_4 : CertificateAt 18 91 4 := by decide +kernel
theorem cell_18_91_5 : CertificateAt 18 91 5 := by decide +kernel
theorem row_18_91 : ThresholdAt 18 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 91 0 cell_18_91_0
    | exact certificate_sound 18 91 1 cell_18_91_1
    | exact certificate_sound 18 91 2 cell_18_91_2
    | exact certificate_sound 18 91 3 cell_18_91_3
    | exact certificate_sound 18 91 4 cell_18_91_4
    | exact certificate_sound 18 91 5 cell_18_91_5
theorem cell_18_92_0 : CertificateAt 18 92 0 := by decide +kernel
theorem cell_18_92_1 : CertificateAt 18 92 1 := by decide +kernel
theorem cell_18_92_2 : CertificateAt 18 92 2 := by decide +kernel
theorem cell_18_92_3 : CertificateAt 18 92 3 := by decide +kernel
theorem cell_18_92_4 : CertificateAt 18 92 4 := by decide +kernel
theorem cell_18_92_5 : CertificateAt 18 92 5 := by decide +kernel
theorem row_18_92 : ThresholdAt 18 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 92 0 cell_18_92_0
    | exact certificate_sound 18 92 1 cell_18_92_1
    | exact certificate_sound 18 92 2 cell_18_92_2
    | exact certificate_sound 18 92 3 cell_18_92_3
    | exact certificate_sound 18 92 4 cell_18_92_4
    | exact certificate_sound 18 92 5 cell_18_92_5
theorem cell_18_93_0 : CertificateAt 18 93 0 := by decide +kernel
theorem cell_18_93_1 : CertificateAt 18 93 1 := by decide +kernel
theorem cell_18_93_2 : CertificateAt 18 93 2 := by decide +kernel
theorem cell_18_93_3 : CertificateAt 18 93 3 := by decide +kernel
theorem cell_18_93_4 : CertificateAt 18 93 4 := by decide +kernel
theorem cell_18_93_5 : CertificateAt 18 93 5 := by decide +kernel
theorem row_18_93 : ThresholdAt 18 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 93 0 cell_18_93_0
    | exact certificate_sound 18 93 1 cell_18_93_1
    | exact certificate_sound 18 93 2 cell_18_93_2
    | exact certificate_sound 18 93 3 cell_18_93_3
    | exact certificate_sound 18 93 4 cell_18_93_4
    | exact certificate_sound 18 93 5 cell_18_93_5
theorem cell_18_94_0 : CertificateAt 18 94 0 := by decide +kernel
theorem cell_18_94_1 : CertificateAt 18 94 1 := by decide +kernel
theorem cell_18_94_2 : CertificateAt 18 94 2 := by decide +kernel
theorem cell_18_94_3 : CertificateAt 18 94 3 := by decide +kernel
theorem cell_18_94_4 : CertificateAt 18 94 4 := by decide +kernel
theorem cell_18_94_5 : CertificateAt 18 94 5 := by decide +kernel
theorem row_18_94 : ThresholdAt 18 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 94 0 cell_18_94_0
    | exact certificate_sound 18 94 1 cell_18_94_1
    | exact certificate_sound 18 94 2 cell_18_94_2
    | exact certificate_sound 18 94 3 cell_18_94_3
    | exact certificate_sound 18 94 4 cell_18_94_4
    | exact certificate_sound 18 94 5 cell_18_94_5
theorem cell_18_95_0 : CertificateAt 18 95 0 := by decide +kernel
theorem cell_18_95_1 : CertificateAt 18 95 1 := by decide +kernel
theorem cell_18_95_2 : CertificateAt 18 95 2 := by decide +kernel
theorem cell_18_95_3 : CertificateAt 18 95 3 := by decide +kernel
theorem cell_18_95_4 : CertificateAt 18 95 4 := by decide +kernel
theorem cell_18_95_5 : CertificateAt 18 95 5 := by decide +kernel
theorem row_18_95 : ThresholdAt 18 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 95 0 cell_18_95_0
    | exact certificate_sound 18 95 1 cell_18_95_1
    | exact certificate_sound 18 95 2 cell_18_95_2
    | exact certificate_sound 18 95 3 cell_18_95_3
    | exact certificate_sound 18 95 4 cell_18_95_4
    | exact certificate_sound 18 95 5 cell_18_95_5
theorem cell_18_96_0 : CertificateAt 18 96 0 := by decide +kernel
theorem cell_18_96_1 : CertificateAt 18 96 1 := by decide +kernel
theorem cell_18_96_2 : CertificateAt 18 96 2 := by decide +kernel
theorem cell_18_96_3 : CertificateAt 18 96 3 := by decide +kernel
theorem cell_18_96_4 : CertificateAt 18 96 4 := by decide +kernel
theorem cell_18_96_5 : CertificateAt 18 96 5 := by decide +kernel
theorem row_18_96 : ThresholdAt 18 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 96 0 cell_18_96_0
    | exact certificate_sound 18 96 1 cell_18_96_1
    | exact certificate_sound 18 96 2 cell_18_96_2
    | exact certificate_sound 18 96 3 cell_18_96_3
    | exact certificate_sound 18 96 4 cell_18_96_4
    | exact certificate_sound 18 96 5 cell_18_96_5
theorem cell_18_97_0 : CertificateAt 18 97 0 := by decide +kernel
theorem cell_18_97_1 : CertificateAt 18 97 1 := by decide +kernel
theorem cell_18_97_2 : CertificateAt 18 97 2 := by decide +kernel
theorem cell_18_97_3 : CertificateAt 18 97 3 := by decide +kernel
theorem cell_18_97_4 : CertificateAt 18 97 4 := by decide +kernel
theorem cell_18_97_5 : CertificateAt 18 97 5 := by decide +kernel
theorem row_18_97 : ThresholdAt 18 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 97 0 cell_18_97_0
    | exact certificate_sound 18 97 1 cell_18_97_1
    | exact certificate_sound 18 97 2 cell_18_97_2
    | exact certificate_sound 18 97 3 cell_18_97_3
    | exact certificate_sound 18 97 4 cell_18_97_4
    | exact certificate_sound 18 97 5 cell_18_97_5
theorem cell_18_98_0 : CertificateAt 18 98 0 := by decide +kernel
theorem cell_18_98_1 : CertificateAt 18 98 1 := by decide +kernel
theorem cell_18_98_2 : CertificateAt 18 98 2 := by decide +kernel
theorem cell_18_98_3 : CertificateAt 18 98 3 := by decide +kernel
theorem cell_18_98_4 : CertificateAt 18 98 4 := by decide +kernel
theorem cell_18_98_5 : CertificateAt 18 98 5 := by decide +kernel
theorem row_18_98 : ThresholdAt 18 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 98 0 cell_18_98_0
    | exact certificate_sound 18 98 1 cell_18_98_1
    | exact certificate_sound 18 98 2 cell_18_98_2
    | exact certificate_sound 18 98 3 cell_18_98_3
    | exact certificate_sound 18 98 4 cell_18_98_4
    | exact certificate_sound 18 98 5 cell_18_98_5
theorem cell_18_99_0 : CertificateAt 18 99 0 := by decide +kernel
theorem cell_18_99_1 : CertificateAt 18 99 1 := by decide +kernel
theorem cell_18_99_2 : CertificateAt 18 99 2 := by decide +kernel
theorem cell_18_99_3 : CertificateAt 18 99 3 := by decide +kernel
theorem cell_18_99_4 : CertificateAt 18 99 4 := by decide +kernel
theorem cell_18_99_5 : CertificateAt 18 99 5 := by decide +kernel
theorem row_18_99 : ThresholdAt 18 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 99 0 cell_18_99_0
    | exact certificate_sound 18 99 1 cell_18_99_1
    | exact certificate_sound 18 99 2 cell_18_99_2
    | exact certificate_sound 18 99 3 cell_18_99_3
    | exact certificate_sound 18 99 4 cell_18_99_4
    | exact certificate_sound 18 99 5 cell_18_99_5
theorem cell_18_100_0 : CertificateAt 18 100 0 := by decide +kernel
theorem cell_18_100_1 : CertificateAt 18 100 1 := by decide +kernel
theorem cell_18_100_2 : CertificateAt 18 100 2 := by decide +kernel
theorem cell_18_100_3 : CertificateAt 18 100 3 := by decide +kernel
theorem cell_18_100_4 : CertificateAt 18 100 4 := by decide +kernel
theorem cell_18_100_5 : CertificateAt 18 100 5 := by decide +kernel
theorem row_18_100 : ThresholdAt 18 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 100 0 cell_18_100_0
    | exact certificate_sound 18 100 1 cell_18_100_1
    | exact certificate_sound 18 100 2 cell_18_100_2
    | exact certificate_sound 18 100 3 cell_18_100_3
    | exact certificate_sound 18 100 4 cell_18_100_4
    | exact certificate_sound 18 100 5 cell_18_100_5
theorem cell_18_101_0 : CertificateAt 18 101 0 := by decide +kernel
theorem cell_18_101_1 : CertificateAt 18 101 1 := by decide +kernel
theorem cell_18_101_2 : CertificateAt 18 101 2 := by decide +kernel
theorem cell_18_101_3 : CertificateAt 18 101 3 := by decide +kernel
theorem cell_18_101_4 : CertificateAt 18 101 4 := by decide +kernel
theorem cell_18_101_5 : CertificateAt 18 101 5 := by decide +kernel
theorem row_18_101 : ThresholdAt 18 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 101 0 cell_18_101_0
    | exact certificate_sound 18 101 1 cell_18_101_1
    | exact certificate_sound 18 101 2 cell_18_101_2
    | exact certificate_sound 18 101 3 cell_18_101_3
    | exact certificate_sound 18 101 4 cell_18_101_4
    | exact certificate_sound 18 101 5 cell_18_101_5
theorem cell_18_102_0 : CertificateAt 18 102 0 := by decide +kernel
theorem cell_18_102_1 : CertificateAt 18 102 1 := by decide +kernel
theorem cell_18_102_2 : CertificateAt 18 102 2 := by decide +kernel
theorem cell_18_102_3 : CertificateAt 18 102 3 := by decide +kernel
theorem cell_18_102_4 : CertificateAt 18 102 4 := by decide +kernel
theorem cell_18_102_5 : CertificateAt 18 102 5 := by decide +kernel
theorem row_18_102 : ThresholdAt 18 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 102 0 cell_18_102_0
    | exact certificate_sound 18 102 1 cell_18_102_1
    | exact certificate_sound 18 102 2 cell_18_102_2
    | exact certificate_sound 18 102 3 cell_18_102_3
    | exact certificate_sound 18 102 4 cell_18_102_4
    | exact certificate_sound 18 102 5 cell_18_102_5
theorem cell_18_103_0 : CertificateAt 18 103 0 := by decide +kernel
theorem cell_18_103_1 : CertificateAt 18 103 1 := by decide +kernel
theorem cell_18_103_2 : CertificateAt 18 103 2 := by decide +kernel
theorem cell_18_103_3 : CertificateAt 18 103 3 := by decide +kernel
theorem cell_18_103_4 : CertificateAt 18 103 4 := by decide +kernel
theorem cell_18_103_5 : CertificateAt 18 103 5 := by decide +kernel
theorem row_18_103 : ThresholdAt 18 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 103 0 cell_18_103_0
    | exact certificate_sound 18 103 1 cell_18_103_1
    | exact certificate_sound 18 103 2 cell_18_103_2
    | exact certificate_sound 18 103 3 cell_18_103_3
    | exact certificate_sound 18 103 4 cell_18_103_4
    | exact certificate_sound 18 103 5 cell_18_103_5
theorem cell_18_104_0 : CertificateAt 18 104 0 := by decide +kernel
theorem cell_18_104_1 : CertificateAt 18 104 1 := by decide +kernel
theorem cell_18_104_2 : CertificateAt 18 104 2 := by decide +kernel
theorem cell_18_104_3 : CertificateAt 18 104 3 := by decide +kernel
theorem cell_18_104_4 : CertificateAt 18 104 4 := by decide +kernel
theorem cell_18_104_5 : CertificateAt 18 104 5 := by decide +kernel
theorem row_18_104 : ThresholdAt 18 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 104 0 cell_18_104_0
    | exact certificate_sound 18 104 1 cell_18_104_1
    | exact certificate_sound 18 104 2 cell_18_104_2
    | exact certificate_sound 18 104 3 cell_18_104_3
    | exact certificate_sound 18 104 4 cell_18_104_4
    | exact certificate_sound 18 104 5 cell_18_104_5
theorem cell_18_105_0 : CertificateAt 18 105 0 := by decide +kernel
theorem cell_18_105_1 : CertificateAt 18 105 1 := by decide +kernel
theorem cell_18_105_2 : CertificateAt 18 105 2 := by decide +kernel
theorem cell_18_105_3 : CertificateAt 18 105 3 := by decide +kernel
theorem cell_18_105_4 : CertificateAt 18 105 4 := by decide +kernel
theorem cell_18_105_5 : CertificateAt 18 105 5 := by decide +kernel
theorem row_18_105 : ThresholdAt 18 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 105 0 cell_18_105_0
    | exact certificate_sound 18 105 1 cell_18_105_1
    | exact certificate_sound 18 105 2 cell_18_105_2
    | exact certificate_sound 18 105 3 cell_18_105_3
    | exact certificate_sound 18 105 4 cell_18_105_4
    | exact certificate_sound 18 105 5 cell_18_105_5
theorem cell_18_106_0 : CertificateAt 18 106 0 := by decide +kernel
theorem cell_18_106_1 : CertificateAt 18 106 1 := by decide +kernel
theorem cell_18_106_2 : CertificateAt 18 106 2 := by decide +kernel
theorem cell_18_106_3 : CertificateAt 18 106 3 := by decide +kernel
theorem cell_18_106_4 : CertificateAt 18 106 4 := by decide +kernel
theorem cell_18_106_5 : CertificateAt 18 106 5 := by decide +kernel
theorem row_18_106 : ThresholdAt 18 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 106 0 cell_18_106_0
    | exact certificate_sound 18 106 1 cell_18_106_1
    | exact certificate_sound 18 106 2 cell_18_106_2
    | exact certificate_sound 18 106 3 cell_18_106_3
    | exact certificate_sound 18 106 4 cell_18_106_4
    | exact certificate_sound 18 106 5 cell_18_106_5
theorem cell_18_107_0 : CertificateAt 18 107 0 := by decide +kernel
theorem cell_18_107_1 : CertificateAt 18 107 1 := by decide +kernel
theorem cell_18_107_2 : CertificateAt 18 107 2 := by decide +kernel
theorem cell_18_107_3 : CertificateAt 18 107 3 := by decide +kernel
theorem cell_18_107_4 : CertificateAt 18 107 4 := by decide +kernel
theorem cell_18_107_5 : CertificateAt 18 107 5 := by decide +kernel
theorem row_18_107 : ThresholdAt 18 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 107 0 cell_18_107_0
    | exact certificate_sound 18 107 1 cell_18_107_1
    | exact certificate_sound 18 107 2 cell_18_107_2
    | exact certificate_sound 18 107 3 cell_18_107_3
    | exact certificate_sound 18 107 4 cell_18_107_4
    | exact certificate_sound 18 107 5 cell_18_107_5
theorem cell_18_108_0 : CertificateAt 18 108 0 := by decide +kernel
theorem cell_18_108_1 : CertificateAt 18 108 1 := by decide +kernel
theorem cell_18_108_2 : CertificateAt 18 108 2 := by decide +kernel
theorem cell_18_108_3 : CertificateAt 18 108 3 := by decide +kernel
theorem cell_18_108_4 : CertificateAt 18 108 4 := by decide +kernel
theorem cell_18_108_5 : CertificateAt 18 108 5 := by decide +kernel
theorem row_18_108 : ThresholdAt 18 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 108 0 cell_18_108_0
    | exact certificate_sound 18 108 1 cell_18_108_1
    | exact certificate_sound 18 108 2 cell_18_108_2
    | exact certificate_sound 18 108 3 cell_18_108_3
    | exact certificate_sound 18 108 4 cell_18_108_4
    | exact certificate_sound 18 108 5 cell_18_108_5
theorem cell_18_109_0 : CertificateAt 18 109 0 := by decide +kernel
theorem cell_18_109_1 : CertificateAt 18 109 1 := by decide +kernel
theorem cell_18_109_2 : CertificateAt 18 109 2 := by decide +kernel
theorem cell_18_109_3 : CertificateAt 18 109 3 := by decide +kernel
theorem cell_18_109_4 : CertificateAt 18 109 4 := by decide +kernel
theorem cell_18_109_5 : CertificateAt 18 109 5 := by decide +kernel
theorem row_18_109 : ThresholdAt 18 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 109 0 cell_18_109_0
    | exact certificate_sound 18 109 1 cell_18_109_1
    | exact certificate_sound 18 109 2 cell_18_109_2
    | exact certificate_sound 18 109 3 cell_18_109_3
    | exact certificate_sound 18 109 4 cell_18_109_4
    | exact certificate_sound 18 109 5 cell_18_109_5
theorem cell_18_110_0 : CertificateAt 18 110 0 := by decide +kernel
theorem cell_18_110_1 : CertificateAt 18 110 1 := by decide +kernel
theorem cell_18_110_2 : CertificateAt 18 110 2 := by decide +kernel
theorem cell_18_110_3 : CertificateAt 18 110 3 := by decide +kernel
theorem cell_18_110_4 : CertificateAt 18 110 4 := by decide +kernel
theorem cell_18_110_5 : CertificateAt 18 110 5 := by decide +kernel
theorem row_18_110 : ThresholdAt 18 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 110 0 cell_18_110_0
    | exact certificate_sound 18 110 1 cell_18_110_1
    | exact certificate_sound 18 110 2 cell_18_110_2
    | exact certificate_sound 18 110 3 cell_18_110_3
    | exact certificate_sound 18 110 4 cell_18_110_4
    | exact certificate_sound 18 110 5 cell_18_110_5
theorem cell_18_111_0 : CertificateAt 18 111 0 := by decide +kernel
theorem cell_18_111_1 : CertificateAt 18 111 1 := by decide +kernel
theorem cell_18_111_2 : CertificateAt 18 111 2 := by decide +kernel
theorem cell_18_111_3 : CertificateAt 18 111 3 := by decide +kernel
theorem cell_18_111_4 : CertificateAt 18 111 4 := by decide +kernel
theorem cell_18_111_5 : CertificateAt 18 111 5 := by decide +kernel
theorem row_18_111 : ThresholdAt 18 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 111 0 cell_18_111_0
    | exact certificate_sound 18 111 1 cell_18_111_1
    | exact certificate_sound 18 111 2 cell_18_111_2
    | exact certificate_sound 18 111 3 cell_18_111_3
    | exact certificate_sound 18 111 4 cell_18_111_4
    | exact certificate_sound 18 111 5 cell_18_111_5
theorem cell_18_112_0 : CertificateAt 18 112 0 := by decide +kernel
theorem cell_18_112_1 : CertificateAt 18 112 1 := by decide +kernel
theorem cell_18_112_2 : CertificateAt 18 112 2 := by decide +kernel
theorem cell_18_112_3 : CertificateAt 18 112 3 := by decide +kernel
theorem cell_18_112_4 : CertificateAt 18 112 4 := by decide +kernel
theorem cell_18_112_5 : CertificateAt 18 112 5 := by decide +kernel
theorem row_18_112 : ThresholdAt 18 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 112 0 cell_18_112_0
    | exact certificate_sound 18 112 1 cell_18_112_1
    | exact certificate_sound 18 112 2 cell_18_112_2
    | exact certificate_sound 18 112 3 cell_18_112_3
    | exact certificate_sound 18 112 4 cell_18_112_4
    | exact certificate_sound 18 112 5 cell_18_112_5
theorem cell_18_113_0 : CertificateAt 18 113 0 := by decide +kernel
theorem cell_18_113_1 : CertificateAt 18 113 1 := by decide +kernel
theorem cell_18_113_2 : CertificateAt 18 113 2 := by decide +kernel
theorem cell_18_113_3 : CertificateAt 18 113 3 := by decide +kernel
theorem cell_18_113_4 : CertificateAt 18 113 4 := by decide +kernel
theorem cell_18_113_5 : CertificateAt 18 113 5 := by decide +kernel
theorem row_18_113 : ThresholdAt 18 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 113 0 cell_18_113_0
    | exact certificate_sound 18 113 1 cell_18_113_1
    | exact certificate_sound 18 113 2 cell_18_113_2
    | exact certificate_sound 18 113 3 cell_18_113_3
    | exact certificate_sound 18 113 4 cell_18_113_4
    | exact certificate_sound 18 113 5 cell_18_113_5
theorem cell_18_114_0 : CertificateAt 18 114 0 := by decide +kernel
theorem cell_18_114_1 : CertificateAt 18 114 1 := by decide +kernel
theorem cell_18_114_2 : CertificateAt 18 114 2 := by decide +kernel
theorem cell_18_114_3 : CertificateAt 18 114 3 := by decide +kernel
theorem cell_18_114_4 : CertificateAt 18 114 4 := by decide +kernel
theorem cell_18_114_5 : CertificateAt 18 114 5 := by decide +kernel
theorem row_18_114 : ThresholdAt 18 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 114 0 cell_18_114_0
    | exact certificate_sound 18 114 1 cell_18_114_1
    | exact certificate_sound 18 114 2 cell_18_114_2
    | exact certificate_sound 18 114 3 cell_18_114_3
    | exact certificate_sound 18 114 4 cell_18_114_4
    | exact certificate_sound 18 114 5 cell_18_114_5
theorem cell_18_115_0 : CertificateAt 18 115 0 := by decide +kernel
theorem cell_18_115_1 : CertificateAt 18 115 1 := by decide +kernel
theorem cell_18_115_2 : CertificateAt 18 115 2 := by decide +kernel
theorem cell_18_115_3 : CertificateAt 18 115 3 := by decide +kernel
theorem cell_18_115_4 : CertificateAt 18 115 4 := by decide +kernel
theorem cell_18_115_5 : CertificateAt 18 115 5 := by decide +kernel
theorem row_18_115 : ThresholdAt 18 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 115 0 cell_18_115_0
    | exact certificate_sound 18 115 1 cell_18_115_1
    | exact certificate_sound 18 115 2 cell_18_115_2
    | exact certificate_sound 18 115 3 cell_18_115_3
    | exact certificate_sound 18 115 4 cell_18_115_4
    | exact certificate_sound 18 115 5 cell_18_115_5
theorem cell_18_116_0 : CertificateAt 18 116 0 := by decide +kernel
theorem cell_18_116_1 : CertificateAt 18 116 1 := by decide +kernel
theorem cell_18_116_2 : CertificateAt 18 116 2 := by decide +kernel
theorem cell_18_116_3 : CertificateAt 18 116 3 := by decide +kernel
theorem cell_18_116_4 : CertificateAt 18 116 4 := by decide +kernel
theorem cell_18_116_5 : CertificateAt 18 116 5 := by decide +kernel
theorem row_18_116 : ThresholdAt 18 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 116 0 cell_18_116_0
    | exact certificate_sound 18 116 1 cell_18_116_1
    | exact certificate_sound 18 116 2 cell_18_116_2
    | exact certificate_sound 18 116 3 cell_18_116_3
    | exact certificate_sound 18 116 4 cell_18_116_4
    | exact certificate_sound 18 116 5 cell_18_116_5
theorem cell_18_117_0 : CertificateAt 18 117 0 := by decide +kernel
theorem cell_18_117_1 : CertificateAt 18 117 1 := by decide +kernel
theorem cell_18_117_2 : CertificateAt 18 117 2 := by decide +kernel
theorem cell_18_117_3 : CertificateAt 18 117 3 := by decide +kernel
theorem cell_18_117_4 : CertificateAt 18 117 4 := by decide +kernel
theorem cell_18_117_5 : CertificateAt 18 117 5 := by decide +kernel
theorem row_18_117 : ThresholdAt 18 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 117 0 cell_18_117_0
    | exact certificate_sound 18 117 1 cell_18_117_1
    | exact certificate_sound 18 117 2 cell_18_117_2
    | exact certificate_sound 18 117 3 cell_18_117_3
    | exact certificate_sound 18 117 4 cell_18_117_4
    | exact certificate_sound 18 117 5 cell_18_117_5
theorem cell_18_118_0 : CertificateAt 18 118 0 := by decide +kernel
theorem cell_18_118_1 : CertificateAt 18 118 1 := by decide +kernel
theorem cell_18_118_2 : CertificateAt 18 118 2 := by decide +kernel
theorem cell_18_118_3 : CertificateAt 18 118 3 := by decide +kernel
theorem cell_18_118_4 : CertificateAt 18 118 4 := by decide +kernel
theorem cell_18_118_5 : CertificateAt 18 118 5 := by decide +kernel
theorem row_18_118 : ThresholdAt 18 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 118 0 cell_18_118_0
    | exact certificate_sound 18 118 1 cell_18_118_1
    | exact certificate_sound 18 118 2 cell_18_118_2
    | exact certificate_sound 18 118 3 cell_18_118_3
    | exact certificate_sound 18 118 4 cell_18_118_4
    | exact certificate_sound 18 118 5 cell_18_118_5
theorem cell_18_119_0 : CertificateAt 18 119 0 := by decide +kernel
theorem cell_18_119_1 : CertificateAt 18 119 1 := by decide +kernel
theorem cell_18_119_2 : CertificateAt 18 119 2 := by decide +kernel
theorem cell_18_119_3 : CertificateAt 18 119 3 := by decide +kernel
theorem cell_18_119_4 : CertificateAt 18 119 4 := by decide +kernel
theorem cell_18_119_5 : CertificateAt 18 119 5 := by decide +kernel
theorem row_18_119 : ThresholdAt 18 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 119 0 cell_18_119_0
    | exact certificate_sound 18 119 1 cell_18_119_1
    | exact certificate_sound 18 119 2 cell_18_119_2
    | exact certificate_sound 18 119 3 cell_18_119_3
    | exact certificate_sound 18 119 4 cell_18_119_4
    | exact certificate_sound 18 119 5 cell_18_119_5
theorem cell_18_120_0 : CertificateAt 18 120 0 := by decide +kernel
theorem cell_18_120_1 : CertificateAt 18 120 1 := by decide +kernel
theorem cell_18_120_2 : CertificateAt 18 120 2 := by decide +kernel
theorem cell_18_120_3 : CertificateAt 18 120 3 := by decide +kernel
theorem cell_18_120_4 : CertificateAt 18 120 4 := by decide +kernel
theorem cell_18_120_5 : CertificateAt 18 120 5 := by decide +kernel
theorem row_18_120 : ThresholdAt 18 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 120 0 cell_18_120_0
    | exact certificate_sound 18 120 1 cell_18_120_1
    | exact certificate_sound 18 120 2 cell_18_120_2
    | exact certificate_sound 18 120 3 cell_18_120_3
    | exact certificate_sound 18 120 4 cell_18_120_4
    | exact certificate_sound 18 120 5 cell_18_120_5
theorem cell_18_121_0 : CertificateAt 18 121 0 := by decide +kernel
theorem cell_18_121_1 : CertificateAt 18 121 1 := by decide +kernel
theorem cell_18_121_2 : CertificateAt 18 121 2 := by decide +kernel
theorem cell_18_121_3 : CertificateAt 18 121 3 := by decide +kernel
theorem cell_18_121_4 : CertificateAt 18 121 4 := by decide +kernel
theorem cell_18_121_5 : CertificateAt 18 121 5 := by decide +kernel
theorem row_18_121 : ThresholdAt 18 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 18 121 0 cell_18_121_0
    | exact certificate_sound 18 121 1 cell_18_121_1
    | exact certificate_sound 18 121 2 cell_18_121_2
    | exact certificate_sound 18 121 3 cell_18_121_3
    | exact certificate_sound 18 121 4 cell_18_121_4
    | exact certificate_sound 18 121 5 cell_18_121_5
theorem checkedR18 : ∀ V ∈ List.range 122, ThresholdAt 18 V := by
  intro V hV
  have hv : V < 122 := List.mem_range.mp hV
  by_cases h0_122 : V < 61
  · by_cases h0_61 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_18_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_18_1
              · have he : V = 2 := by omega
                subst V
                exact row_18_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_18_3
              · have he : V = 4 := by omega
                subst V
                exact row_18_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_18_5
              · have he : V = 6 := by omega
                subst V
                exact row_18_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_18_7
              · have he : V = 8 := by omega
                subst V
                exact row_18_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_18_9
              · have he : V = 10 := by omega
                subst V
                exact row_18_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_18_11
              · have he : V = 12 := by omega
                subst V
                exact row_18_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_18_13
              · have he : V = 14 := by omega
                subst V
                exact row_18_14
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have he : V = 15 := by omega
              subst V
              exact row_18_15
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_18_16
              · have he : V = 17 := by omega
                subst V
                exact row_18_17
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_18_18
              · have he : V = 19 := by omega
                subst V
                exact row_18_19
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_18_20
              · have he : V = 21 := by omega
                subst V
                exact row_18_21
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_18_22
              · have he : V = 23 := by omega
                subst V
                exact row_18_23
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_18_24
              · have he : V = 25 := by omega
                subst V
                exact row_18_25
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_18_26
              · have he : V = 27 := by omega
                subst V
                exact row_18_27
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_18_28
              · have he : V = 29 := by omega
                subst V
                exact row_18_29
    · by_cases h30_61 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have he : V = 30 := by omega
              subst V
              exact row_18_30
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_18_31
              · have he : V = 32 := by omega
                subst V
                exact row_18_32
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_18_33
              · have he : V = 34 := by omega
                subst V
                exact row_18_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_18_35
              · have he : V = 36 := by omega
                subst V
                exact row_18_36
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_18_37
              · have he : V = 38 := by omega
                subst V
                exact row_18_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_18_39
              · have he : V = 40 := by omega
                subst V
                exact row_18_40
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_18_41
              · have he : V = 42 := by omega
                subst V
                exact row_18_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_18_43
              · have he : V = 44 := by omega
                subst V
                exact row_18_44
      · by_cases h45_61 : V < 53
        · by_cases h45_53 : V < 49
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_18_45
              · have he : V = 46 := by omega
                subst V
                exact row_18_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_18_47
              · have he : V = 48 := by omega
                subst V
                exact row_18_48
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_18_49
              · have he : V = 50 := by omega
                subst V
                exact row_18_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_18_51
              · have he : V = 52 := by omega
                subst V
                exact row_18_52
        · by_cases h53_61 : V < 57
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_18_53
              · have he : V = 54 := by omega
                subst V
                exact row_18_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_18_55
              · have he : V = 56 := by omega
                subst V
                exact row_18_56
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_18_57
              · have he : V = 58 := by omega
                subst V
                exact row_18_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_18_59
              · have he : V = 60 := by omega
                subst V
                exact row_18_60
  · by_cases h61_122 : V < 91
    · by_cases h61_91 : V < 76
      · by_cases h61_76 : V < 68
        · by_cases h61_68 : V < 64
          · by_cases h61_64 : V < 62
            · have he : V = 61 := by omega
              subst V
              exact row_18_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_18_62
              · have he : V = 63 := by omega
                subst V
                exact row_18_63
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_18_64
              · have he : V = 65 := by omega
                subst V
                exact row_18_65
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_18_66
              · have he : V = 67 := by omega
                subst V
                exact row_18_67
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_18_68
              · have he : V = 69 := by omega
                subst V
                exact row_18_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_18_70
              · have he : V = 71 := by omega
                subst V
                exact row_18_71
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_18_72
              · have he : V = 73 := by omega
                subst V
                exact row_18_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_18_74
              · have he : V = 75 := by omega
                subst V
                exact row_18_75
      · by_cases h76_91 : V < 83
        · by_cases h76_83 : V < 79
          · by_cases h76_79 : V < 77
            · have he : V = 76 := by omega
              subst V
              exact row_18_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_18_77
              · have he : V = 78 := by omega
                subst V
                exact row_18_78
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_18_79
              · have he : V = 80 := by omega
                subst V
                exact row_18_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_18_81
              · have he : V = 82 := by omega
                subst V
                exact row_18_82
        · by_cases h83_91 : V < 87
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_18_83
              · have he : V = 84 := by omega
                subst V
                exact row_18_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_18_85
              · have he : V = 86 := by omega
                subst V
                exact row_18_86
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_18_87
              · have he : V = 88 := by omega
                subst V
                exact row_18_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_18_89
              · have he : V = 90 := by omega
                subst V
                exact row_18_90
    · by_cases h91_122 : V < 106
      · by_cases h91_106 : V < 98
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have he : V = 91 := by omega
              subst V
              exact row_18_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_18_92
              · have he : V = 93 := by omega
                subst V
                exact row_18_93
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_18_94
              · have he : V = 95 := by omega
                subst V
                exact row_18_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_18_96
              · have he : V = 97 := by omega
                subst V
                exact row_18_97
        · by_cases h98_106 : V < 102
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_18_98
              · have he : V = 99 := by omega
                subst V
                exact row_18_99
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_18_100
              · have he : V = 101 := by omega
                subst V
                exact row_18_101
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_18_102
              · have he : V = 103 := by omega
                subst V
                exact row_18_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_18_104
              · have he : V = 105 := by omega
                subst V
                exact row_18_105
      · by_cases h106_122 : V < 114
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_18_106
              · have he : V = 107 := by omega
                subst V
                exact row_18_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_18_108
              · have he : V = 109 := by omega
                subst V
                exact row_18_109
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_18_110
              · have he : V = 111 := by omega
                subst V
                exact row_18_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_18_112
              · have he : V = 113 := by omega
                subst V
                exact row_18_113
        · by_cases h114_122 : V < 118
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_18_114
              · have he : V = 115 := by omega
                subst V
                exact row_18_115
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_18_116
              · have he : V = 117 := by omega
                subst V
                exact row_18_117
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_18_118
              · have he : V = 119 := by omega
                subst V
                exact row_18_119
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_18_120
              · have he : V = 121 := by omega
                subst V
                exact row_18_121
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
