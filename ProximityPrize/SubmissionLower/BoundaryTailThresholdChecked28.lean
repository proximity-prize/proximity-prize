import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked27

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_28_0_0 : CertificateAt 28 0 0 := by decide +kernel
theorem cell_28_0_1 : CertificateAt 28 0 1 := by decide +kernel
theorem cell_28_0_2 : CertificateAt 28 0 2 := by decide +kernel
theorem cell_28_0_3 : CertificateAt 28 0 3 := by decide +kernel
theorem cell_28_0_4 : CertificateAt 28 0 4 := by decide +kernel
theorem cell_28_0_5 : CertificateAt 28 0 5 := by decide +kernel
theorem row_28_0 : ThresholdAt 28 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 0 0 cell_28_0_0
    | exact certificate_sound 28 0 1 cell_28_0_1
    | exact certificate_sound 28 0 2 cell_28_0_2
    | exact certificate_sound 28 0 3 cell_28_0_3
    | exact certificate_sound 28 0 4 cell_28_0_4
    | exact certificate_sound 28 0 5 cell_28_0_5
theorem cell_28_1_0 : CertificateAt 28 1 0 := by decide +kernel
theorem cell_28_1_1 : CertificateAt 28 1 1 := by decide +kernel
theorem cell_28_1_2 : CertificateAt 28 1 2 := by decide +kernel
theorem cell_28_1_3 : CertificateAt 28 1 3 := by decide +kernel
theorem cell_28_1_4 : CertificateAt 28 1 4 := by decide +kernel
theorem cell_28_1_5 : CertificateAt 28 1 5 := by decide +kernel
theorem row_28_1 : ThresholdAt 28 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 1 0 cell_28_1_0
    | exact certificate_sound 28 1 1 cell_28_1_1
    | exact certificate_sound 28 1 2 cell_28_1_2
    | exact certificate_sound 28 1 3 cell_28_1_3
    | exact certificate_sound 28 1 4 cell_28_1_4
    | exact certificate_sound 28 1 5 cell_28_1_5
theorem cell_28_2_0 : CertificateAt 28 2 0 := by decide +kernel
theorem cell_28_2_1 : CertificateAt 28 2 1 := by decide +kernel
theorem cell_28_2_2 : CertificateAt 28 2 2 := by decide +kernel
theorem cell_28_2_3 : CertificateAt 28 2 3 := by decide +kernel
theorem cell_28_2_4 : CertificateAt 28 2 4 := by decide +kernel
theorem cell_28_2_5 : CertificateAt 28 2 5 := by decide +kernel
theorem row_28_2 : ThresholdAt 28 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 2 0 cell_28_2_0
    | exact certificate_sound 28 2 1 cell_28_2_1
    | exact certificate_sound 28 2 2 cell_28_2_2
    | exact certificate_sound 28 2 3 cell_28_2_3
    | exact certificate_sound 28 2 4 cell_28_2_4
    | exact certificate_sound 28 2 5 cell_28_2_5
theorem cell_28_3_0 : CertificateAt 28 3 0 := by decide +kernel
theorem cell_28_3_1 : CertificateAt 28 3 1 := by decide +kernel
theorem cell_28_3_2 : CertificateAt 28 3 2 := by decide +kernel
theorem cell_28_3_3 : CertificateAt 28 3 3 := by decide +kernel
theorem cell_28_3_4 : CertificateAt 28 3 4 := by decide +kernel
theorem cell_28_3_5 : CertificateAt 28 3 5 := by decide +kernel
theorem row_28_3 : ThresholdAt 28 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 3 0 cell_28_3_0
    | exact certificate_sound 28 3 1 cell_28_3_1
    | exact certificate_sound 28 3 2 cell_28_3_2
    | exact certificate_sound 28 3 3 cell_28_3_3
    | exact certificate_sound 28 3 4 cell_28_3_4
    | exact certificate_sound 28 3 5 cell_28_3_5
theorem cell_28_4_0 : CertificateAt 28 4 0 := by decide +kernel
theorem cell_28_4_1 : CertificateAt 28 4 1 := by decide +kernel
theorem cell_28_4_2 : CertificateAt 28 4 2 := by decide +kernel
theorem cell_28_4_3 : CertificateAt 28 4 3 := by decide +kernel
theorem cell_28_4_4 : CertificateAt 28 4 4 := by decide +kernel
theorem cell_28_4_5 : CertificateAt 28 4 5 := by decide +kernel
theorem row_28_4 : ThresholdAt 28 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 4 0 cell_28_4_0
    | exact certificate_sound 28 4 1 cell_28_4_1
    | exact certificate_sound 28 4 2 cell_28_4_2
    | exact certificate_sound 28 4 3 cell_28_4_3
    | exact certificate_sound 28 4 4 cell_28_4_4
    | exact certificate_sound 28 4 5 cell_28_4_5
theorem cell_28_5_0 : CertificateAt 28 5 0 := by decide +kernel
theorem cell_28_5_1 : CertificateAt 28 5 1 := by decide +kernel
theorem cell_28_5_2 : CertificateAt 28 5 2 := by decide +kernel
theorem cell_28_5_3 : CertificateAt 28 5 3 := by decide +kernel
theorem cell_28_5_4 : CertificateAt 28 5 4 := by decide +kernel
theorem cell_28_5_5 : CertificateAt 28 5 5 := by decide +kernel
theorem row_28_5 : ThresholdAt 28 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 5 0 cell_28_5_0
    | exact certificate_sound 28 5 1 cell_28_5_1
    | exact certificate_sound 28 5 2 cell_28_5_2
    | exact certificate_sound 28 5 3 cell_28_5_3
    | exact certificate_sound 28 5 4 cell_28_5_4
    | exact certificate_sound 28 5 5 cell_28_5_5
theorem cell_28_6_0 : CertificateAt 28 6 0 := by decide +kernel
theorem cell_28_6_1 : CertificateAt 28 6 1 := by decide +kernel
theorem cell_28_6_2 : CertificateAt 28 6 2 := by decide +kernel
theorem cell_28_6_3 : CertificateAt 28 6 3 := by decide +kernel
theorem cell_28_6_4 : CertificateAt 28 6 4 := by decide +kernel
theorem cell_28_6_5 : CertificateAt 28 6 5 := by decide +kernel
theorem row_28_6 : ThresholdAt 28 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 6 0 cell_28_6_0
    | exact certificate_sound 28 6 1 cell_28_6_1
    | exact certificate_sound 28 6 2 cell_28_6_2
    | exact certificate_sound 28 6 3 cell_28_6_3
    | exact certificate_sound 28 6 4 cell_28_6_4
    | exact certificate_sound 28 6 5 cell_28_6_5
theorem cell_28_7_0 : CertificateAt 28 7 0 := by decide +kernel
theorem cell_28_7_1 : CertificateAt 28 7 1 := by decide +kernel
theorem cell_28_7_2 : CertificateAt 28 7 2 := by decide +kernel
theorem cell_28_7_3 : CertificateAt 28 7 3 := by decide +kernel
theorem cell_28_7_4 : CertificateAt 28 7 4 := by decide +kernel
theorem cell_28_7_5 : CertificateAt 28 7 5 := by decide +kernel
theorem row_28_7 : ThresholdAt 28 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 7 0 cell_28_7_0
    | exact certificate_sound 28 7 1 cell_28_7_1
    | exact certificate_sound 28 7 2 cell_28_7_2
    | exact certificate_sound 28 7 3 cell_28_7_3
    | exact certificate_sound 28 7 4 cell_28_7_4
    | exact certificate_sound 28 7 5 cell_28_7_5
theorem cell_28_8_0 : CertificateAt 28 8 0 := by decide +kernel
theorem cell_28_8_1 : CertificateAt 28 8 1 := by decide +kernel
theorem cell_28_8_2 : CertificateAt 28 8 2 := by decide +kernel
theorem cell_28_8_3 : CertificateAt 28 8 3 := by decide +kernel
theorem cell_28_8_4 : CertificateAt 28 8 4 := by decide +kernel
theorem cell_28_8_5 : CertificateAt 28 8 5 := by decide +kernel
theorem row_28_8 : ThresholdAt 28 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 8 0 cell_28_8_0
    | exact certificate_sound 28 8 1 cell_28_8_1
    | exact certificate_sound 28 8 2 cell_28_8_2
    | exact certificate_sound 28 8 3 cell_28_8_3
    | exact certificate_sound 28 8 4 cell_28_8_4
    | exact certificate_sound 28 8 5 cell_28_8_5
theorem cell_28_9_0 : CertificateAt 28 9 0 := by decide +kernel
theorem cell_28_9_1 : CertificateAt 28 9 1 := by decide +kernel
theorem cell_28_9_2 : CertificateAt 28 9 2 := by decide +kernel
theorem cell_28_9_3 : CertificateAt 28 9 3 := by decide +kernel
theorem cell_28_9_4 : CertificateAt 28 9 4 := by decide +kernel
theorem cell_28_9_5 : CertificateAt 28 9 5 := by decide +kernel
theorem row_28_9 : ThresholdAt 28 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 9 0 cell_28_9_0
    | exact certificate_sound 28 9 1 cell_28_9_1
    | exact certificate_sound 28 9 2 cell_28_9_2
    | exact certificate_sound 28 9 3 cell_28_9_3
    | exact certificate_sound 28 9 4 cell_28_9_4
    | exact certificate_sound 28 9 5 cell_28_9_5
theorem cell_28_10_0 : CertificateAt 28 10 0 := by decide +kernel
theorem cell_28_10_1 : CertificateAt 28 10 1 := by decide +kernel
theorem cell_28_10_2 : CertificateAt 28 10 2 := by decide +kernel
theorem cell_28_10_3 : CertificateAt 28 10 3 := by decide +kernel
theorem cell_28_10_4 : CertificateAt 28 10 4 := by decide +kernel
theorem cell_28_10_5 : CertificateAt 28 10 5 := by decide +kernel
theorem row_28_10 : ThresholdAt 28 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 10 0 cell_28_10_0
    | exact certificate_sound 28 10 1 cell_28_10_1
    | exact certificate_sound 28 10 2 cell_28_10_2
    | exact certificate_sound 28 10 3 cell_28_10_3
    | exact certificate_sound 28 10 4 cell_28_10_4
    | exact certificate_sound 28 10 5 cell_28_10_5
theorem cell_28_11_0 : CertificateAt 28 11 0 := by decide +kernel
theorem cell_28_11_1 : CertificateAt 28 11 1 := by decide +kernel
theorem cell_28_11_2 : CertificateAt 28 11 2 := by decide +kernel
theorem cell_28_11_3 : CertificateAt 28 11 3 := by decide +kernel
theorem cell_28_11_4 : CertificateAt 28 11 4 := by decide +kernel
theorem cell_28_11_5 : CertificateAt 28 11 5 := by decide +kernel
theorem row_28_11 : ThresholdAt 28 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 11 0 cell_28_11_0
    | exact certificate_sound 28 11 1 cell_28_11_1
    | exact certificate_sound 28 11 2 cell_28_11_2
    | exact certificate_sound 28 11 3 cell_28_11_3
    | exact certificate_sound 28 11 4 cell_28_11_4
    | exact certificate_sound 28 11 5 cell_28_11_5
theorem cell_28_12_0 : CertificateAt 28 12 0 := by decide +kernel
theorem cell_28_12_1 : CertificateAt 28 12 1 := by decide +kernel
theorem cell_28_12_2 : CertificateAt 28 12 2 := by decide +kernel
theorem cell_28_12_3 : CertificateAt 28 12 3 := by decide +kernel
theorem cell_28_12_4 : CertificateAt 28 12 4 := by decide +kernel
theorem cell_28_12_5 : CertificateAt 28 12 5 := by decide +kernel
theorem row_28_12 : ThresholdAt 28 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 12 0 cell_28_12_0
    | exact certificate_sound 28 12 1 cell_28_12_1
    | exact certificate_sound 28 12 2 cell_28_12_2
    | exact certificate_sound 28 12 3 cell_28_12_3
    | exact certificate_sound 28 12 4 cell_28_12_4
    | exact certificate_sound 28 12 5 cell_28_12_5
theorem cell_28_13_0 : CertificateAt 28 13 0 := by decide +kernel
theorem cell_28_13_1 : CertificateAt 28 13 1 := by decide +kernel
theorem cell_28_13_2 : CertificateAt 28 13 2 := by decide +kernel
theorem cell_28_13_3 : CertificateAt 28 13 3 := by decide +kernel
theorem cell_28_13_4 : CertificateAt 28 13 4 := by decide +kernel
theorem cell_28_13_5 : CertificateAt 28 13 5 := by decide +kernel
theorem row_28_13 : ThresholdAt 28 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 13 0 cell_28_13_0
    | exact certificate_sound 28 13 1 cell_28_13_1
    | exact certificate_sound 28 13 2 cell_28_13_2
    | exact certificate_sound 28 13 3 cell_28_13_3
    | exact certificate_sound 28 13 4 cell_28_13_4
    | exact certificate_sound 28 13 5 cell_28_13_5
theorem cell_28_14_0 : CertificateAt 28 14 0 := by decide +kernel
theorem cell_28_14_1 : CertificateAt 28 14 1 := by decide +kernel
theorem cell_28_14_2 : CertificateAt 28 14 2 := by decide +kernel
theorem cell_28_14_3 : CertificateAt 28 14 3 := by decide +kernel
theorem cell_28_14_4 : CertificateAt 28 14 4 := by decide +kernel
theorem cell_28_14_5 : CertificateAt 28 14 5 := by decide +kernel
theorem row_28_14 : ThresholdAt 28 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 14 0 cell_28_14_0
    | exact certificate_sound 28 14 1 cell_28_14_1
    | exact certificate_sound 28 14 2 cell_28_14_2
    | exact certificate_sound 28 14 3 cell_28_14_3
    | exact certificate_sound 28 14 4 cell_28_14_4
    | exact certificate_sound 28 14 5 cell_28_14_5
theorem cell_28_15_0 : CertificateAt 28 15 0 := by decide +kernel
theorem cell_28_15_1 : CertificateAt 28 15 1 := by decide +kernel
theorem cell_28_15_2 : CertificateAt 28 15 2 := by decide +kernel
theorem cell_28_15_3 : CertificateAt 28 15 3 := by decide +kernel
theorem cell_28_15_4 : CertificateAt 28 15 4 := by decide +kernel
theorem cell_28_15_5 : CertificateAt 28 15 5 := by decide +kernel
theorem row_28_15 : ThresholdAt 28 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 15 0 cell_28_15_0
    | exact certificate_sound 28 15 1 cell_28_15_1
    | exact certificate_sound 28 15 2 cell_28_15_2
    | exact certificate_sound 28 15 3 cell_28_15_3
    | exact certificate_sound 28 15 4 cell_28_15_4
    | exact certificate_sound 28 15 5 cell_28_15_5
theorem cell_28_16_0 : CertificateAt 28 16 0 := by decide +kernel
theorem cell_28_16_1 : CertificateAt 28 16 1 := by decide +kernel
theorem cell_28_16_2 : CertificateAt 28 16 2 := by decide +kernel
theorem cell_28_16_3 : CertificateAt 28 16 3 := by decide +kernel
theorem cell_28_16_4 : CertificateAt 28 16 4 := by decide +kernel
theorem cell_28_16_5 : CertificateAt 28 16 5 := by decide +kernel
theorem row_28_16 : ThresholdAt 28 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 16 0 cell_28_16_0
    | exact certificate_sound 28 16 1 cell_28_16_1
    | exact certificate_sound 28 16 2 cell_28_16_2
    | exact certificate_sound 28 16 3 cell_28_16_3
    | exact certificate_sound 28 16 4 cell_28_16_4
    | exact certificate_sound 28 16 5 cell_28_16_5
theorem cell_28_17_0 : CertificateAt 28 17 0 := by decide +kernel
theorem cell_28_17_1 : CertificateAt 28 17 1 := by decide +kernel
theorem cell_28_17_2 : CertificateAt 28 17 2 := by decide +kernel
theorem cell_28_17_3 : CertificateAt 28 17 3 := by decide +kernel
theorem cell_28_17_4 : CertificateAt 28 17 4 := by decide +kernel
theorem cell_28_17_5 : CertificateAt 28 17 5 := by decide +kernel
theorem row_28_17 : ThresholdAt 28 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 17 0 cell_28_17_0
    | exact certificate_sound 28 17 1 cell_28_17_1
    | exact certificate_sound 28 17 2 cell_28_17_2
    | exact certificate_sound 28 17 3 cell_28_17_3
    | exact certificate_sound 28 17 4 cell_28_17_4
    | exact certificate_sound 28 17 5 cell_28_17_5
theorem cell_28_18_0 : CertificateAt 28 18 0 := by decide +kernel
theorem cell_28_18_1 : CertificateAt 28 18 1 := by decide +kernel
theorem cell_28_18_2 : CertificateAt 28 18 2 := by decide +kernel
theorem cell_28_18_3 : CertificateAt 28 18 3 := by decide +kernel
theorem cell_28_18_4 : CertificateAt 28 18 4 := by decide +kernel
theorem cell_28_18_5 : CertificateAt 28 18 5 := by decide +kernel
theorem row_28_18 : ThresholdAt 28 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 18 0 cell_28_18_0
    | exact certificate_sound 28 18 1 cell_28_18_1
    | exact certificate_sound 28 18 2 cell_28_18_2
    | exact certificate_sound 28 18 3 cell_28_18_3
    | exact certificate_sound 28 18 4 cell_28_18_4
    | exact certificate_sound 28 18 5 cell_28_18_5
theorem cell_28_19_0 : CertificateAt 28 19 0 := by decide +kernel
theorem cell_28_19_1 : CertificateAt 28 19 1 := by decide +kernel
theorem cell_28_19_2 : CertificateAt 28 19 2 := by decide +kernel
theorem cell_28_19_3 : CertificateAt 28 19 3 := by decide +kernel
theorem cell_28_19_4 : CertificateAt 28 19 4 := by decide +kernel
theorem cell_28_19_5 : CertificateAt 28 19 5 := by decide +kernel
theorem row_28_19 : ThresholdAt 28 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 19 0 cell_28_19_0
    | exact certificate_sound 28 19 1 cell_28_19_1
    | exact certificate_sound 28 19 2 cell_28_19_2
    | exact certificate_sound 28 19 3 cell_28_19_3
    | exact certificate_sound 28 19 4 cell_28_19_4
    | exact certificate_sound 28 19 5 cell_28_19_5
theorem cell_28_20_0 : CertificateAt 28 20 0 := by decide +kernel
theorem cell_28_20_1 : CertificateAt 28 20 1 := by decide +kernel
theorem cell_28_20_2 : CertificateAt 28 20 2 := by decide +kernel
theorem cell_28_20_3 : CertificateAt 28 20 3 := by decide +kernel
theorem cell_28_20_4 : CertificateAt 28 20 4 := by decide +kernel
theorem cell_28_20_5 : CertificateAt 28 20 5 := by decide +kernel
theorem row_28_20 : ThresholdAt 28 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 20 0 cell_28_20_0
    | exact certificate_sound 28 20 1 cell_28_20_1
    | exact certificate_sound 28 20 2 cell_28_20_2
    | exact certificate_sound 28 20 3 cell_28_20_3
    | exact certificate_sound 28 20 4 cell_28_20_4
    | exact certificate_sound 28 20 5 cell_28_20_5
theorem cell_28_21_0 : CertificateAt 28 21 0 := by decide +kernel
theorem cell_28_21_1 : CertificateAt 28 21 1 := by decide +kernel
theorem cell_28_21_2 : CertificateAt 28 21 2 := by decide +kernel
theorem cell_28_21_3 : CertificateAt 28 21 3 := by decide +kernel
theorem cell_28_21_4 : CertificateAt 28 21 4 := by decide +kernel
theorem cell_28_21_5 : CertificateAt 28 21 5 := by decide +kernel
theorem row_28_21 : ThresholdAt 28 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 21 0 cell_28_21_0
    | exact certificate_sound 28 21 1 cell_28_21_1
    | exact certificate_sound 28 21 2 cell_28_21_2
    | exact certificate_sound 28 21 3 cell_28_21_3
    | exact certificate_sound 28 21 4 cell_28_21_4
    | exact certificate_sound 28 21 5 cell_28_21_5
theorem cell_28_22_0 : CertificateAt 28 22 0 := by decide +kernel
theorem cell_28_22_1 : CertificateAt 28 22 1 := by decide +kernel
theorem cell_28_22_2 : CertificateAt 28 22 2 := by decide +kernel
theorem cell_28_22_3 : CertificateAt 28 22 3 := by decide +kernel
theorem cell_28_22_4 : CertificateAt 28 22 4 := by decide +kernel
theorem cell_28_22_5 : CertificateAt 28 22 5 := by decide +kernel
theorem row_28_22 : ThresholdAt 28 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 22 0 cell_28_22_0
    | exact certificate_sound 28 22 1 cell_28_22_1
    | exact certificate_sound 28 22 2 cell_28_22_2
    | exact certificate_sound 28 22 3 cell_28_22_3
    | exact certificate_sound 28 22 4 cell_28_22_4
    | exact certificate_sound 28 22 5 cell_28_22_5
theorem cell_28_23_0 : CertificateAt 28 23 0 := by decide +kernel
theorem cell_28_23_1 : CertificateAt 28 23 1 := by decide +kernel
theorem cell_28_23_2 : CertificateAt 28 23 2 := by decide +kernel
theorem cell_28_23_3 : CertificateAt 28 23 3 := by decide +kernel
theorem cell_28_23_4 : CertificateAt 28 23 4 := by decide +kernel
theorem cell_28_23_5 : CertificateAt 28 23 5 := by decide +kernel
theorem row_28_23 : ThresholdAt 28 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 23 0 cell_28_23_0
    | exact certificate_sound 28 23 1 cell_28_23_1
    | exact certificate_sound 28 23 2 cell_28_23_2
    | exact certificate_sound 28 23 3 cell_28_23_3
    | exact certificate_sound 28 23 4 cell_28_23_4
    | exact certificate_sound 28 23 5 cell_28_23_5
theorem cell_28_24_0 : CertificateAt 28 24 0 := by decide +kernel
theorem cell_28_24_1 : CertificateAt 28 24 1 := by decide +kernel
theorem cell_28_24_2 : CertificateAt 28 24 2 := by decide +kernel
theorem cell_28_24_3 : CertificateAt 28 24 3 := by decide +kernel
theorem cell_28_24_4 : CertificateAt 28 24 4 := by decide +kernel
theorem cell_28_24_5 : CertificateAt 28 24 5 := by decide +kernel
theorem row_28_24 : ThresholdAt 28 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 24 0 cell_28_24_0
    | exact certificate_sound 28 24 1 cell_28_24_1
    | exact certificate_sound 28 24 2 cell_28_24_2
    | exact certificate_sound 28 24 3 cell_28_24_3
    | exact certificate_sound 28 24 4 cell_28_24_4
    | exact certificate_sound 28 24 5 cell_28_24_5
theorem cell_28_25_0 : CertificateAt 28 25 0 := by decide +kernel
theorem cell_28_25_1 : CertificateAt 28 25 1 := by decide +kernel
theorem cell_28_25_2 : CertificateAt 28 25 2 := by decide +kernel
theorem cell_28_25_3 : CertificateAt 28 25 3 := by decide +kernel
theorem cell_28_25_4 : CertificateAt 28 25 4 := by decide +kernel
theorem cell_28_25_5 : CertificateAt 28 25 5 := by decide +kernel
theorem row_28_25 : ThresholdAt 28 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 25 0 cell_28_25_0
    | exact certificate_sound 28 25 1 cell_28_25_1
    | exact certificate_sound 28 25 2 cell_28_25_2
    | exact certificate_sound 28 25 3 cell_28_25_3
    | exact certificate_sound 28 25 4 cell_28_25_4
    | exact certificate_sound 28 25 5 cell_28_25_5
theorem cell_28_26_0 : CertificateAt 28 26 0 := by decide +kernel
theorem cell_28_26_1 : CertificateAt 28 26 1 := by decide +kernel
theorem cell_28_26_2 : CertificateAt 28 26 2 := by decide +kernel
theorem cell_28_26_3 : CertificateAt 28 26 3 := by decide +kernel
theorem cell_28_26_4 : CertificateAt 28 26 4 := by decide +kernel
theorem cell_28_26_5 : CertificateAt 28 26 5 := by decide +kernel
theorem row_28_26 : ThresholdAt 28 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 26 0 cell_28_26_0
    | exact certificate_sound 28 26 1 cell_28_26_1
    | exact certificate_sound 28 26 2 cell_28_26_2
    | exact certificate_sound 28 26 3 cell_28_26_3
    | exact certificate_sound 28 26 4 cell_28_26_4
    | exact certificate_sound 28 26 5 cell_28_26_5
theorem cell_28_27_0 : CertificateAt 28 27 0 := by decide +kernel
theorem cell_28_27_1 : CertificateAt 28 27 1 := by decide +kernel
theorem cell_28_27_2 : CertificateAt 28 27 2 := by decide +kernel
theorem cell_28_27_3 : CertificateAt 28 27 3 := by decide +kernel
theorem cell_28_27_4 : CertificateAt 28 27 4 := by decide +kernel
theorem cell_28_27_5 : CertificateAt 28 27 5 := by decide +kernel
theorem row_28_27 : ThresholdAt 28 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 27 0 cell_28_27_0
    | exact certificate_sound 28 27 1 cell_28_27_1
    | exact certificate_sound 28 27 2 cell_28_27_2
    | exact certificate_sound 28 27 3 cell_28_27_3
    | exact certificate_sound 28 27 4 cell_28_27_4
    | exact certificate_sound 28 27 5 cell_28_27_5
theorem cell_28_28_0 : CertificateAt 28 28 0 := by decide +kernel
theorem cell_28_28_1 : CertificateAt 28 28 1 := by decide +kernel
theorem cell_28_28_2 : CertificateAt 28 28 2 := by decide +kernel
theorem cell_28_28_3 : CertificateAt 28 28 3 := by decide +kernel
theorem cell_28_28_4 : CertificateAt 28 28 4 := by decide +kernel
theorem cell_28_28_5 : CertificateAt 28 28 5 := by decide +kernel
theorem row_28_28 : ThresholdAt 28 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 28 0 cell_28_28_0
    | exact certificate_sound 28 28 1 cell_28_28_1
    | exact certificate_sound 28 28 2 cell_28_28_2
    | exact certificate_sound 28 28 3 cell_28_28_3
    | exact certificate_sound 28 28 4 cell_28_28_4
    | exact certificate_sound 28 28 5 cell_28_28_5
theorem cell_28_29_0 : CertificateAt 28 29 0 := by decide +kernel
theorem cell_28_29_1 : CertificateAt 28 29 1 := by decide +kernel
theorem cell_28_29_2 : CertificateAt 28 29 2 := by decide +kernel
theorem cell_28_29_3 : CertificateAt 28 29 3 := by decide +kernel
theorem cell_28_29_4 : CertificateAt 28 29 4 := by decide +kernel
theorem cell_28_29_5 : CertificateAt 28 29 5 := by decide +kernel
theorem row_28_29 : ThresholdAt 28 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 29 0 cell_28_29_0
    | exact certificate_sound 28 29 1 cell_28_29_1
    | exact certificate_sound 28 29 2 cell_28_29_2
    | exact certificate_sound 28 29 3 cell_28_29_3
    | exact certificate_sound 28 29 4 cell_28_29_4
    | exact certificate_sound 28 29 5 cell_28_29_5
theorem cell_28_30_0 : CertificateAt 28 30 0 := by decide +kernel
theorem cell_28_30_1 : CertificateAt 28 30 1 := by decide +kernel
theorem cell_28_30_2 : CertificateAt 28 30 2 := by decide +kernel
theorem cell_28_30_3 : CertificateAt 28 30 3 := by decide +kernel
theorem cell_28_30_4 : CertificateAt 28 30 4 := by decide +kernel
theorem cell_28_30_5 : CertificateAt 28 30 5 := by decide +kernel
theorem row_28_30 : ThresholdAt 28 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 30 0 cell_28_30_0
    | exact certificate_sound 28 30 1 cell_28_30_1
    | exact certificate_sound 28 30 2 cell_28_30_2
    | exact certificate_sound 28 30 3 cell_28_30_3
    | exact certificate_sound 28 30 4 cell_28_30_4
    | exact certificate_sound 28 30 5 cell_28_30_5
theorem cell_28_31_0 : CertificateAt 28 31 0 := by decide +kernel
theorem cell_28_31_1 : CertificateAt 28 31 1 := by decide +kernel
theorem cell_28_31_2 : CertificateAt 28 31 2 := by decide +kernel
theorem cell_28_31_3 : CertificateAt 28 31 3 := by decide +kernel
theorem cell_28_31_4 : CertificateAt 28 31 4 := by decide +kernel
theorem cell_28_31_5 : CertificateAt 28 31 5 := by decide +kernel
theorem row_28_31 : ThresholdAt 28 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 31 0 cell_28_31_0
    | exact certificate_sound 28 31 1 cell_28_31_1
    | exact certificate_sound 28 31 2 cell_28_31_2
    | exact certificate_sound 28 31 3 cell_28_31_3
    | exact certificate_sound 28 31 4 cell_28_31_4
    | exact certificate_sound 28 31 5 cell_28_31_5
theorem cell_28_32_0 : CertificateAt 28 32 0 := by decide +kernel
theorem cell_28_32_1 : CertificateAt 28 32 1 := by decide +kernel
theorem cell_28_32_2 : CertificateAt 28 32 2 := by decide +kernel
theorem cell_28_32_3 : CertificateAt 28 32 3 := by decide +kernel
theorem cell_28_32_4 : CertificateAt 28 32 4 := by decide +kernel
theorem cell_28_32_5 : CertificateAt 28 32 5 := by decide +kernel
theorem row_28_32 : ThresholdAt 28 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 32 0 cell_28_32_0
    | exact certificate_sound 28 32 1 cell_28_32_1
    | exact certificate_sound 28 32 2 cell_28_32_2
    | exact certificate_sound 28 32 3 cell_28_32_3
    | exact certificate_sound 28 32 4 cell_28_32_4
    | exact certificate_sound 28 32 5 cell_28_32_5
theorem cell_28_33_0 : CertificateAt 28 33 0 := by decide +kernel
theorem cell_28_33_1 : CertificateAt 28 33 1 := by decide +kernel
theorem cell_28_33_2 : CertificateAt 28 33 2 := by decide +kernel
theorem cell_28_33_3 : CertificateAt 28 33 3 := by decide +kernel
theorem cell_28_33_4 : CertificateAt 28 33 4 := by decide +kernel
theorem cell_28_33_5 : CertificateAt 28 33 5 := by decide +kernel
theorem row_28_33 : ThresholdAt 28 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 33 0 cell_28_33_0
    | exact certificate_sound 28 33 1 cell_28_33_1
    | exact certificate_sound 28 33 2 cell_28_33_2
    | exact certificate_sound 28 33 3 cell_28_33_3
    | exact certificate_sound 28 33 4 cell_28_33_4
    | exact certificate_sound 28 33 5 cell_28_33_5
theorem cell_28_34_0 : CertificateAt 28 34 0 := by decide +kernel
theorem cell_28_34_1 : CertificateAt 28 34 1 := by decide +kernel
theorem cell_28_34_2 : CertificateAt 28 34 2 := by decide +kernel
theorem cell_28_34_3 : CertificateAt 28 34 3 := by decide +kernel
theorem cell_28_34_4 : CertificateAt 28 34 4 := by decide +kernel
theorem cell_28_34_5 : CertificateAt 28 34 5 := by decide +kernel
theorem row_28_34 : ThresholdAt 28 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 34 0 cell_28_34_0
    | exact certificate_sound 28 34 1 cell_28_34_1
    | exact certificate_sound 28 34 2 cell_28_34_2
    | exact certificate_sound 28 34 3 cell_28_34_3
    | exact certificate_sound 28 34 4 cell_28_34_4
    | exact certificate_sound 28 34 5 cell_28_34_5
theorem cell_28_35_0 : CertificateAt 28 35 0 := by decide +kernel
theorem cell_28_35_1 : CertificateAt 28 35 1 := by decide +kernel
theorem cell_28_35_2 : CertificateAt 28 35 2 := by decide +kernel
theorem cell_28_35_3 : CertificateAt 28 35 3 := by decide +kernel
theorem cell_28_35_4 : CertificateAt 28 35 4 := by decide +kernel
theorem cell_28_35_5 : CertificateAt 28 35 5 := by decide +kernel
theorem row_28_35 : ThresholdAt 28 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 35 0 cell_28_35_0
    | exact certificate_sound 28 35 1 cell_28_35_1
    | exact certificate_sound 28 35 2 cell_28_35_2
    | exact certificate_sound 28 35 3 cell_28_35_3
    | exact certificate_sound 28 35 4 cell_28_35_4
    | exact certificate_sound 28 35 5 cell_28_35_5
theorem cell_28_36_0 : CertificateAt 28 36 0 := by decide +kernel
theorem cell_28_36_1 : CertificateAt 28 36 1 := by decide +kernel
theorem cell_28_36_2 : CertificateAt 28 36 2 := by decide +kernel
theorem cell_28_36_3 : CertificateAt 28 36 3 := by decide +kernel
theorem cell_28_36_4 : CertificateAt 28 36 4 := by decide +kernel
theorem cell_28_36_5 : CertificateAt 28 36 5 := by decide +kernel
theorem row_28_36 : ThresholdAt 28 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 36 0 cell_28_36_0
    | exact certificate_sound 28 36 1 cell_28_36_1
    | exact certificate_sound 28 36 2 cell_28_36_2
    | exact certificate_sound 28 36 3 cell_28_36_3
    | exact certificate_sound 28 36 4 cell_28_36_4
    | exact certificate_sound 28 36 5 cell_28_36_5
theorem cell_28_37_0 : CertificateAt 28 37 0 := by decide +kernel
theorem cell_28_37_1 : CertificateAt 28 37 1 := by decide +kernel
theorem cell_28_37_2 : CertificateAt 28 37 2 := by decide +kernel
theorem cell_28_37_3 : CertificateAt 28 37 3 := by decide +kernel
theorem cell_28_37_4 : CertificateAt 28 37 4 := by decide +kernel
theorem cell_28_37_5 : CertificateAt 28 37 5 := by decide +kernel
theorem row_28_37 : ThresholdAt 28 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 37 0 cell_28_37_0
    | exact certificate_sound 28 37 1 cell_28_37_1
    | exact certificate_sound 28 37 2 cell_28_37_2
    | exact certificate_sound 28 37 3 cell_28_37_3
    | exact certificate_sound 28 37 4 cell_28_37_4
    | exact certificate_sound 28 37 5 cell_28_37_5
theorem cell_28_38_0 : CertificateAt 28 38 0 := by decide +kernel
theorem cell_28_38_1 : CertificateAt 28 38 1 := by decide +kernel
theorem cell_28_38_2 : CertificateAt 28 38 2 := by decide +kernel
theorem cell_28_38_3 : CertificateAt 28 38 3 := by decide +kernel
theorem cell_28_38_4 : CertificateAt 28 38 4 := by decide +kernel
theorem cell_28_38_5 : CertificateAt 28 38 5 := by decide +kernel
theorem row_28_38 : ThresholdAt 28 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 38 0 cell_28_38_0
    | exact certificate_sound 28 38 1 cell_28_38_1
    | exact certificate_sound 28 38 2 cell_28_38_2
    | exact certificate_sound 28 38 3 cell_28_38_3
    | exact certificate_sound 28 38 4 cell_28_38_4
    | exact certificate_sound 28 38 5 cell_28_38_5
theorem cell_28_39_0 : CertificateAt 28 39 0 := by decide +kernel
theorem cell_28_39_1 : CertificateAt 28 39 1 := by decide +kernel
theorem cell_28_39_2 : CertificateAt 28 39 2 := by decide +kernel
theorem cell_28_39_3 : CertificateAt 28 39 3 := by decide +kernel
theorem cell_28_39_4 : CertificateAt 28 39 4 := by decide +kernel
theorem cell_28_39_5 : CertificateAt 28 39 5 := by decide +kernel
theorem row_28_39 : ThresholdAt 28 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 39 0 cell_28_39_0
    | exact certificate_sound 28 39 1 cell_28_39_1
    | exact certificate_sound 28 39 2 cell_28_39_2
    | exact certificate_sound 28 39 3 cell_28_39_3
    | exact certificate_sound 28 39 4 cell_28_39_4
    | exact certificate_sound 28 39 5 cell_28_39_5
theorem cell_28_40_0 : CertificateAt 28 40 0 := by decide +kernel
theorem cell_28_40_1 : CertificateAt 28 40 1 := by decide +kernel
theorem cell_28_40_2 : CertificateAt 28 40 2 := by decide +kernel
theorem cell_28_40_3 : CertificateAt 28 40 3 := by decide +kernel
theorem cell_28_40_4 : CertificateAt 28 40 4 := by decide +kernel
theorem cell_28_40_5 : CertificateAt 28 40 5 := by decide +kernel
theorem row_28_40 : ThresholdAt 28 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 40 0 cell_28_40_0
    | exact certificate_sound 28 40 1 cell_28_40_1
    | exact certificate_sound 28 40 2 cell_28_40_2
    | exact certificate_sound 28 40 3 cell_28_40_3
    | exact certificate_sound 28 40 4 cell_28_40_4
    | exact certificate_sound 28 40 5 cell_28_40_5
theorem cell_28_41_0 : CertificateAt 28 41 0 := by decide +kernel
theorem cell_28_41_1 : CertificateAt 28 41 1 := by decide +kernel
theorem cell_28_41_2 : CertificateAt 28 41 2 := by decide +kernel
theorem cell_28_41_3 : CertificateAt 28 41 3 := by decide +kernel
theorem cell_28_41_4 : CertificateAt 28 41 4 := by decide +kernel
theorem cell_28_41_5 : CertificateAt 28 41 5 := by decide +kernel
theorem row_28_41 : ThresholdAt 28 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 41 0 cell_28_41_0
    | exact certificate_sound 28 41 1 cell_28_41_1
    | exact certificate_sound 28 41 2 cell_28_41_2
    | exact certificate_sound 28 41 3 cell_28_41_3
    | exact certificate_sound 28 41 4 cell_28_41_4
    | exact certificate_sound 28 41 5 cell_28_41_5
theorem cell_28_42_0 : CertificateAt 28 42 0 := by decide +kernel
theorem cell_28_42_1 : CertificateAt 28 42 1 := by decide +kernel
theorem cell_28_42_2 : CertificateAt 28 42 2 := by decide +kernel
theorem cell_28_42_3 : CertificateAt 28 42 3 := by decide +kernel
theorem cell_28_42_4 : CertificateAt 28 42 4 := by decide +kernel
theorem cell_28_42_5 : CertificateAt 28 42 5 := by decide +kernel
theorem row_28_42 : ThresholdAt 28 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 42 0 cell_28_42_0
    | exact certificate_sound 28 42 1 cell_28_42_1
    | exact certificate_sound 28 42 2 cell_28_42_2
    | exact certificate_sound 28 42 3 cell_28_42_3
    | exact certificate_sound 28 42 4 cell_28_42_4
    | exact certificate_sound 28 42 5 cell_28_42_5
theorem cell_28_43_0 : CertificateAt 28 43 0 := by decide +kernel
theorem cell_28_43_1 : CertificateAt 28 43 1 := by decide +kernel
theorem cell_28_43_2 : CertificateAt 28 43 2 := by decide +kernel
theorem cell_28_43_3 : CertificateAt 28 43 3 := by decide +kernel
theorem cell_28_43_4 : CertificateAt 28 43 4 := by decide +kernel
theorem cell_28_43_5 : CertificateAt 28 43 5 := by decide +kernel
theorem row_28_43 : ThresholdAt 28 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 43 0 cell_28_43_0
    | exact certificate_sound 28 43 1 cell_28_43_1
    | exact certificate_sound 28 43 2 cell_28_43_2
    | exact certificate_sound 28 43 3 cell_28_43_3
    | exact certificate_sound 28 43 4 cell_28_43_4
    | exact certificate_sound 28 43 5 cell_28_43_5
theorem cell_28_44_0 : CertificateAt 28 44 0 := by decide +kernel
theorem cell_28_44_1 : CertificateAt 28 44 1 := by decide +kernel
theorem cell_28_44_2 : CertificateAt 28 44 2 := by decide +kernel
theorem cell_28_44_3 : CertificateAt 28 44 3 := by decide +kernel
theorem cell_28_44_4 : CertificateAt 28 44 4 := by decide +kernel
theorem cell_28_44_5 : CertificateAt 28 44 5 := by decide +kernel
theorem row_28_44 : ThresholdAt 28 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 44 0 cell_28_44_0
    | exact certificate_sound 28 44 1 cell_28_44_1
    | exact certificate_sound 28 44 2 cell_28_44_2
    | exact certificate_sound 28 44 3 cell_28_44_3
    | exact certificate_sound 28 44 4 cell_28_44_4
    | exact certificate_sound 28 44 5 cell_28_44_5
theorem cell_28_45_0 : CertificateAt 28 45 0 := by decide +kernel
theorem cell_28_45_1 : CertificateAt 28 45 1 := by decide +kernel
theorem cell_28_45_2 : CertificateAt 28 45 2 := by decide +kernel
theorem cell_28_45_3 : CertificateAt 28 45 3 := by decide +kernel
theorem cell_28_45_4 : CertificateAt 28 45 4 := by decide +kernel
theorem cell_28_45_5 : CertificateAt 28 45 5 := by decide +kernel
theorem row_28_45 : ThresholdAt 28 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 45 0 cell_28_45_0
    | exact certificate_sound 28 45 1 cell_28_45_1
    | exact certificate_sound 28 45 2 cell_28_45_2
    | exact certificate_sound 28 45 3 cell_28_45_3
    | exact certificate_sound 28 45 4 cell_28_45_4
    | exact certificate_sound 28 45 5 cell_28_45_5
theorem cell_28_46_0 : CertificateAt 28 46 0 := by decide +kernel
theorem cell_28_46_1 : CertificateAt 28 46 1 := by decide +kernel
theorem cell_28_46_2 : CertificateAt 28 46 2 := by decide +kernel
theorem cell_28_46_3 : CertificateAt 28 46 3 := by decide +kernel
theorem cell_28_46_4 : CertificateAt 28 46 4 := by decide +kernel
theorem cell_28_46_5 : CertificateAt 28 46 5 := by decide +kernel
theorem row_28_46 : ThresholdAt 28 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 46 0 cell_28_46_0
    | exact certificate_sound 28 46 1 cell_28_46_1
    | exact certificate_sound 28 46 2 cell_28_46_2
    | exact certificate_sound 28 46 3 cell_28_46_3
    | exact certificate_sound 28 46 4 cell_28_46_4
    | exact certificate_sound 28 46 5 cell_28_46_5
theorem cell_28_47_0 : CertificateAt 28 47 0 := by decide +kernel
theorem cell_28_47_1 : CertificateAt 28 47 1 := by decide +kernel
theorem cell_28_47_2 : CertificateAt 28 47 2 := by decide +kernel
theorem cell_28_47_3 : CertificateAt 28 47 3 := by decide +kernel
theorem cell_28_47_4 : CertificateAt 28 47 4 := by decide +kernel
theorem cell_28_47_5 : CertificateAt 28 47 5 := by decide +kernel
theorem row_28_47 : ThresholdAt 28 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 47 0 cell_28_47_0
    | exact certificate_sound 28 47 1 cell_28_47_1
    | exact certificate_sound 28 47 2 cell_28_47_2
    | exact certificate_sound 28 47 3 cell_28_47_3
    | exact certificate_sound 28 47 4 cell_28_47_4
    | exact certificate_sound 28 47 5 cell_28_47_5
theorem cell_28_48_0 : CertificateAt 28 48 0 := by decide +kernel
theorem cell_28_48_1 : CertificateAt 28 48 1 := by decide +kernel
theorem cell_28_48_2 : CertificateAt 28 48 2 := by decide +kernel
theorem cell_28_48_3 : CertificateAt 28 48 3 := by decide +kernel
theorem cell_28_48_4 : CertificateAt 28 48 4 := by decide +kernel
theorem cell_28_48_5 : CertificateAt 28 48 5 := by decide +kernel
theorem row_28_48 : ThresholdAt 28 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 48 0 cell_28_48_0
    | exact certificate_sound 28 48 1 cell_28_48_1
    | exact certificate_sound 28 48 2 cell_28_48_2
    | exact certificate_sound 28 48 3 cell_28_48_3
    | exact certificate_sound 28 48 4 cell_28_48_4
    | exact certificate_sound 28 48 5 cell_28_48_5
theorem cell_28_49_0 : CertificateAt 28 49 0 := by decide +kernel
theorem cell_28_49_1 : CertificateAt 28 49 1 := by decide +kernel
theorem cell_28_49_2 : CertificateAt 28 49 2 := by decide +kernel
theorem cell_28_49_3 : CertificateAt 28 49 3 := by decide +kernel
theorem cell_28_49_4 : CertificateAt 28 49 4 := by decide +kernel
theorem cell_28_49_5 : CertificateAt 28 49 5 := by decide +kernel
theorem row_28_49 : ThresholdAt 28 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 49 0 cell_28_49_0
    | exact certificate_sound 28 49 1 cell_28_49_1
    | exact certificate_sound 28 49 2 cell_28_49_2
    | exact certificate_sound 28 49 3 cell_28_49_3
    | exact certificate_sound 28 49 4 cell_28_49_4
    | exact certificate_sound 28 49 5 cell_28_49_5
theorem cell_28_50_0 : CertificateAt 28 50 0 := by decide +kernel
theorem cell_28_50_1 : CertificateAt 28 50 1 := by decide +kernel
theorem cell_28_50_2 : CertificateAt 28 50 2 := by decide +kernel
theorem cell_28_50_3 : CertificateAt 28 50 3 := by decide +kernel
theorem cell_28_50_4 : CertificateAt 28 50 4 := by decide +kernel
theorem cell_28_50_5 : CertificateAt 28 50 5 := by decide +kernel
theorem row_28_50 : ThresholdAt 28 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 50 0 cell_28_50_0
    | exact certificate_sound 28 50 1 cell_28_50_1
    | exact certificate_sound 28 50 2 cell_28_50_2
    | exact certificate_sound 28 50 3 cell_28_50_3
    | exact certificate_sound 28 50 4 cell_28_50_4
    | exact certificate_sound 28 50 5 cell_28_50_5
theorem cell_28_51_0 : CertificateAt 28 51 0 := by decide +kernel
theorem cell_28_51_1 : CertificateAt 28 51 1 := by decide +kernel
theorem cell_28_51_2 : CertificateAt 28 51 2 := by decide +kernel
theorem cell_28_51_3 : CertificateAt 28 51 3 := by decide +kernel
theorem cell_28_51_4 : CertificateAt 28 51 4 := by decide +kernel
theorem cell_28_51_5 : CertificateAt 28 51 5 := by decide +kernel
theorem row_28_51 : ThresholdAt 28 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 51 0 cell_28_51_0
    | exact certificate_sound 28 51 1 cell_28_51_1
    | exact certificate_sound 28 51 2 cell_28_51_2
    | exact certificate_sound 28 51 3 cell_28_51_3
    | exact certificate_sound 28 51 4 cell_28_51_4
    | exact certificate_sound 28 51 5 cell_28_51_5
theorem cell_28_52_0 : CertificateAt 28 52 0 := by decide +kernel
theorem cell_28_52_1 : CertificateAt 28 52 1 := by decide +kernel
theorem cell_28_52_2 : CertificateAt 28 52 2 := by decide +kernel
theorem cell_28_52_3 : CertificateAt 28 52 3 := by decide +kernel
theorem cell_28_52_4 : CertificateAt 28 52 4 := by decide +kernel
theorem cell_28_52_5 : CertificateAt 28 52 5 := by decide +kernel
theorem row_28_52 : ThresholdAt 28 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 52 0 cell_28_52_0
    | exact certificate_sound 28 52 1 cell_28_52_1
    | exact certificate_sound 28 52 2 cell_28_52_2
    | exact certificate_sound 28 52 3 cell_28_52_3
    | exact certificate_sound 28 52 4 cell_28_52_4
    | exact certificate_sound 28 52 5 cell_28_52_5
theorem cell_28_53_0 : CertificateAt 28 53 0 := by decide +kernel
theorem cell_28_53_1 : CertificateAt 28 53 1 := by decide +kernel
theorem cell_28_53_2 : CertificateAt 28 53 2 := by decide +kernel
theorem cell_28_53_3 : CertificateAt 28 53 3 := by decide +kernel
theorem cell_28_53_4 : CertificateAt 28 53 4 := by decide +kernel
theorem cell_28_53_5 : CertificateAt 28 53 5 := by decide +kernel
theorem row_28_53 : ThresholdAt 28 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 53 0 cell_28_53_0
    | exact certificate_sound 28 53 1 cell_28_53_1
    | exact certificate_sound 28 53 2 cell_28_53_2
    | exact certificate_sound 28 53 3 cell_28_53_3
    | exact certificate_sound 28 53 4 cell_28_53_4
    | exact certificate_sound 28 53 5 cell_28_53_5
theorem cell_28_54_0 : CertificateAt 28 54 0 := by decide +kernel
theorem cell_28_54_1 : CertificateAt 28 54 1 := by decide +kernel
theorem cell_28_54_2 : CertificateAt 28 54 2 := by decide +kernel
theorem cell_28_54_3 : CertificateAt 28 54 3 := by decide +kernel
theorem cell_28_54_4 : CertificateAt 28 54 4 := by decide +kernel
theorem cell_28_54_5 : CertificateAt 28 54 5 := by decide +kernel
theorem row_28_54 : ThresholdAt 28 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 54 0 cell_28_54_0
    | exact certificate_sound 28 54 1 cell_28_54_1
    | exact certificate_sound 28 54 2 cell_28_54_2
    | exact certificate_sound 28 54 3 cell_28_54_3
    | exact certificate_sound 28 54 4 cell_28_54_4
    | exact certificate_sound 28 54 5 cell_28_54_5
theorem cell_28_55_0 : CertificateAt 28 55 0 := by decide +kernel
theorem cell_28_55_1 : CertificateAt 28 55 1 := by decide +kernel
theorem cell_28_55_2 : CertificateAt 28 55 2 := by decide +kernel
theorem cell_28_55_3 : CertificateAt 28 55 3 := by decide +kernel
theorem cell_28_55_4 : CertificateAt 28 55 4 := by decide +kernel
theorem cell_28_55_5 : CertificateAt 28 55 5 := by decide +kernel
theorem row_28_55 : ThresholdAt 28 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 55 0 cell_28_55_0
    | exact certificate_sound 28 55 1 cell_28_55_1
    | exact certificate_sound 28 55 2 cell_28_55_2
    | exact certificate_sound 28 55 3 cell_28_55_3
    | exact certificate_sound 28 55 4 cell_28_55_4
    | exact certificate_sound 28 55 5 cell_28_55_5
theorem cell_28_56_0 : CertificateAt 28 56 0 := by decide +kernel
theorem cell_28_56_1 : CertificateAt 28 56 1 := by decide +kernel
theorem cell_28_56_2 : CertificateAt 28 56 2 := by decide +kernel
theorem cell_28_56_3 : CertificateAt 28 56 3 := by decide +kernel
theorem cell_28_56_4 : CertificateAt 28 56 4 := by decide +kernel
theorem cell_28_56_5 : CertificateAt 28 56 5 := by decide +kernel
theorem row_28_56 : ThresholdAt 28 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 56 0 cell_28_56_0
    | exact certificate_sound 28 56 1 cell_28_56_1
    | exact certificate_sound 28 56 2 cell_28_56_2
    | exact certificate_sound 28 56 3 cell_28_56_3
    | exact certificate_sound 28 56 4 cell_28_56_4
    | exact certificate_sound 28 56 5 cell_28_56_5
theorem cell_28_57_0 : CertificateAt 28 57 0 := by decide +kernel
theorem cell_28_57_1 : CertificateAt 28 57 1 := by decide +kernel
theorem cell_28_57_2 : CertificateAt 28 57 2 := by decide +kernel
theorem cell_28_57_3 : CertificateAt 28 57 3 := by decide +kernel
theorem cell_28_57_4 : CertificateAt 28 57 4 := by decide +kernel
theorem cell_28_57_5 : CertificateAt 28 57 5 := by decide +kernel
theorem row_28_57 : ThresholdAt 28 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 57 0 cell_28_57_0
    | exact certificate_sound 28 57 1 cell_28_57_1
    | exact certificate_sound 28 57 2 cell_28_57_2
    | exact certificate_sound 28 57 3 cell_28_57_3
    | exact certificate_sound 28 57 4 cell_28_57_4
    | exact certificate_sound 28 57 5 cell_28_57_5
theorem cell_28_58_0 : CertificateAt 28 58 0 := by decide +kernel
theorem cell_28_58_1 : CertificateAt 28 58 1 := by decide +kernel
theorem cell_28_58_2 : CertificateAt 28 58 2 := by decide +kernel
theorem cell_28_58_3 : CertificateAt 28 58 3 := by decide +kernel
theorem cell_28_58_4 : CertificateAt 28 58 4 := by decide +kernel
theorem cell_28_58_5 : CertificateAt 28 58 5 := by decide +kernel
theorem row_28_58 : ThresholdAt 28 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 58 0 cell_28_58_0
    | exact certificate_sound 28 58 1 cell_28_58_1
    | exact certificate_sound 28 58 2 cell_28_58_2
    | exact certificate_sound 28 58 3 cell_28_58_3
    | exact certificate_sound 28 58 4 cell_28_58_4
    | exact certificate_sound 28 58 5 cell_28_58_5
theorem cell_28_59_0 : CertificateAt 28 59 0 := by decide +kernel
theorem cell_28_59_1 : CertificateAt 28 59 1 := by decide +kernel
theorem cell_28_59_2 : CertificateAt 28 59 2 := by decide +kernel
theorem cell_28_59_3 : CertificateAt 28 59 3 := by decide +kernel
theorem cell_28_59_4 : CertificateAt 28 59 4 := by decide +kernel
theorem cell_28_59_5 : CertificateAt 28 59 5 := by decide +kernel
theorem row_28_59 : ThresholdAt 28 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 59 0 cell_28_59_0
    | exact certificate_sound 28 59 1 cell_28_59_1
    | exact certificate_sound 28 59 2 cell_28_59_2
    | exact certificate_sound 28 59 3 cell_28_59_3
    | exact certificate_sound 28 59 4 cell_28_59_4
    | exact certificate_sound 28 59 5 cell_28_59_5
theorem cell_28_60_0 : CertificateAt 28 60 0 := by decide +kernel
theorem cell_28_60_1 : CertificateAt 28 60 1 := by decide +kernel
theorem cell_28_60_2 : CertificateAt 28 60 2 := by decide +kernel
theorem cell_28_60_3 : CertificateAt 28 60 3 := by decide +kernel
theorem cell_28_60_4 : CertificateAt 28 60 4 := by decide +kernel
theorem cell_28_60_5 : CertificateAt 28 60 5 := by decide +kernel
theorem row_28_60 : ThresholdAt 28 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 60 0 cell_28_60_0
    | exact certificate_sound 28 60 1 cell_28_60_1
    | exact certificate_sound 28 60 2 cell_28_60_2
    | exact certificate_sound 28 60 3 cell_28_60_3
    | exact certificate_sound 28 60 4 cell_28_60_4
    | exact certificate_sound 28 60 5 cell_28_60_5
theorem cell_28_61_0 : CertificateAt 28 61 0 := by decide +kernel
theorem cell_28_61_1 : CertificateAt 28 61 1 := by decide +kernel
theorem cell_28_61_2 : CertificateAt 28 61 2 := by decide +kernel
theorem cell_28_61_3 : CertificateAt 28 61 3 := by decide +kernel
theorem cell_28_61_4 : CertificateAt 28 61 4 := by decide +kernel
theorem cell_28_61_5 : CertificateAt 28 61 5 := by decide +kernel
theorem row_28_61 : ThresholdAt 28 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 61 0 cell_28_61_0
    | exact certificate_sound 28 61 1 cell_28_61_1
    | exact certificate_sound 28 61 2 cell_28_61_2
    | exact certificate_sound 28 61 3 cell_28_61_3
    | exact certificate_sound 28 61 4 cell_28_61_4
    | exact certificate_sound 28 61 5 cell_28_61_5
theorem cell_28_62_0 : CertificateAt 28 62 0 := by decide +kernel
theorem cell_28_62_1 : CertificateAt 28 62 1 := by decide +kernel
theorem cell_28_62_2 : CertificateAt 28 62 2 := by decide +kernel
theorem cell_28_62_3 : CertificateAt 28 62 3 := by decide +kernel
theorem cell_28_62_4 : CertificateAt 28 62 4 := by decide +kernel
theorem cell_28_62_5 : CertificateAt 28 62 5 := by decide +kernel
theorem row_28_62 : ThresholdAt 28 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 62 0 cell_28_62_0
    | exact certificate_sound 28 62 1 cell_28_62_1
    | exact certificate_sound 28 62 2 cell_28_62_2
    | exact certificate_sound 28 62 3 cell_28_62_3
    | exact certificate_sound 28 62 4 cell_28_62_4
    | exact certificate_sound 28 62 5 cell_28_62_5
theorem cell_28_63_0 : CertificateAt 28 63 0 := by decide +kernel
theorem cell_28_63_1 : CertificateAt 28 63 1 := by decide +kernel
theorem cell_28_63_2 : CertificateAt 28 63 2 := by decide +kernel
theorem cell_28_63_3 : CertificateAt 28 63 3 := by decide +kernel
theorem cell_28_63_4 : CertificateAt 28 63 4 := by decide +kernel
theorem cell_28_63_5 : CertificateAt 28 63 5 := by decide +kernel
theorem row_28_63 : ThresholdAt 28 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 63 0 cell_28_63_0
    | exact certificate_sound 28 63 1 cell_28_63_1
    | exact certificate_sound 28 63 2 cell_28_63_2
    | exact certificate_sound 28 63 3 cell_28_63_3
    | exact certificate_sound 28 63 4 cell_28_63_4
    | exact certificate_sound 28 63 5 cell_28_63_5
theorem cell_28_64_0 : CertificateAt 28 64 0 := by decide +kernel
theorem cell_28_64_1 : CertificateAt 28 64 1 := by decide +kernel
theorem cell_28_64_2 : CertificateAt 28 64 2 := by decide +kernel
theorem cell_28_64_3 : CertificateAt 28 64 3 := by decide +kernel
theorem cell_28_64_4 : CertificateAt 28 64 4 := by decide +kernel
theorem cell_28_64_5 : CertificateAt 28 64 5 := by decide +kernel
theorem row_28_64 : ThresholdAt 28 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 64 0 cell_28_64_0
    | exact certificate_sound 28 64 1 cell_28_64_1
    | exact certificate_sound 28 64 2 cell_28_64_2
    | exact certificate_sound 28 64 3 cell_28_64_3
    | exact certificate_sound 28 64 4 cell_28_64_4
    | exact certificate_sound 28 64 5 cell_28_64_5
theorem cell_28_65_0 : CertificateAt 28 65 0 := by decide +kernel
theorem cell_28_65_1 : CertificateAt 28 65 1 := by decide +kernel
theorem cell_28_65_2 : CertificateAt 28 65 2 := by decide +kernel
theorem cell_28_65_3 : CertificateAt 28 65 3 := by decide +kernel
theorem cell_28_65_4 : CertificateAt 28 65 4 := by decide +kernel
theorem cell_28_65_5 : CertificateAt 28 65 5 := by decide +kernel
theorem row_28_65 : ThresholdAt 28 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 65 0 cell_28_65_0
    | exact certificate_sound 28 65 1 cell_28_65_1
    | exact certificate_sound 28 65 2 cell_28_65_2
    | exact certificate_sound 28 65 3 cell_28_65_3
    | exact certificate_sound 28 65 4 cell_28_65_4
    | exact certificate_sound 28 65 5 cell_28_65_5
theorem cell_28_66_0 : CertificateAt 28 66 0 := by decide +kernel
theorem cell_28_66_1 : CertificateAt 28 66 1 := by decide +kernel
theorem cell_28_66_2 : CertificateAt 28 66 2 := by decide +kernel
theorem cell_28_66_3 : CertificateAt 28 66 3 := by decide +kernel
theorem cell_28_66_4 : CertificateAt 28 66 4 := by decide +kernel
theorem cell_28_66_5 : CertificateAt 28 66 5 := by decide +kernel
theorem row_28_66 : ThresholdAt 28 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 66 0 cell_28_66_0
    | exact certificate_sound 28 66 1 cell_28_66_1
    | exact certificate_sound 28 66 2 cell_28_66_2
    | exact certificate_sound 28 66 3 cell_28_66_3
    | exact certificate_sound 28 66 4 cell_28_66_4
    | exact certificate_sound 28 66 5 cell_28_66_5
theorem cell_28_67_0 : CertificateAt 28 67 0 := by decide +kernel
theorem cell_28_67_1 : CertificateAt 28 67 1 := by decide +kernel
theorem cell_28_67_2 : CertificateAt 28 67 2 := by decide +kernel
theorem cell_28_67_3 : CertificateAt 28 67 3 := by decide +kernel
theorem cell_28_67_4 : CertificateAt 28 67 4 := by decide +kernel
theorem cell_28_67_5 : CertificateAt 28 67 5 := by decide +kernel
theorem row_28_67 : ThresholdAt 28 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 67 0 cell_28_67_0
    | exact certificate_sound 28 67 1 cell_28_67_1
    | exact certificate_sound 28 67 2 cell_28_67_2
    | exact certificate_sound 28 67 3 cell_28_67_3
    | exact certificate_sound 28 67 4 cell_28_67_4
    | exact certificate_sound 28 67 5 cell_28_67_5
theorem cell_28_68_0 : CertificateAt 28 68 0 := by decide +kernel
theorem cell_28_68_1 : CertificateAt 28 68 1 := by decide +kernel
theorem cell_28_68_2 : CertificateAt 28 68 2 := by decide +kernel
theorem cell_28_68_3 : CertificateAt 28 68 3 := by decide +kernel
theorem cell_28_68_4 : CertificateAt 28 68 4 := by decide +kernel
theorem cell_28_68_5 : CertificateAt 28 68 5 := by decide +kernel
theorem row_28_68 : ThresholdAt 28 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 68 0 cell_28_68_0
    | exact certificate_sound 28 68 1 cell_28_68_1
    | exact certificate_sound 28 68 2 cell_28_68_2
    | exact certificate_sound 28 68 3 cell_28_68_3
    | exact certificate_sound 28 68 4 cell_28_68_4
    | exact certificate_sound 28 68 5 cell_28_68_5
theorem cell_28_69_0 : CertificateAt 28 69 0 := by decide +kernel
theorem cell_28_69_1 : CertificateAt 28 69 1 := by decide +kernel
theorem cell_28_69_2 : CertificateAt 28 69 2 := by decide +kernel
theorem cell_28_69_3 : CertificateAt 28 69 3 := by decide +kernel
theorem cell_28_69_4 : CertificateAt 28 69 4 := by decide +kernel
theorem cell_28_69_5 : CertificateAt 28 69 5 := by decide +kernel
theorem row_28_69 : ThresholdAt 28 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 69 0 cell_28_69_0
    | exact certificate_sound 28 69 1 cell_28_69_1
    | exact certificate_sound 28 69 2 cell_28_69_2
    | exact certificate_sound 28 69 3 cell_28_69_3
    | exact certificate_sound 28 69 4 cell_28_69_4
    | exact certificate_sound 28 69 5 cell_28_69_5
theorem cell_28_70_0 : CertificateAt 28 70 0 := by decide +kernel
theorem cell_28_70_1 : CertificateAt 28 70 1 := by decide +kernel
theorem cell_28_70_2 : CertificateAt 28 70 2 := by decide +kernel
theorem cell_28_70_3 : CertificateAt 28 70 3 := by decide +kernel
theorem cell_28_70_4 : CertificateAt 28 70 4 := by decide +kernel
theorem cell_28_70_5 : CertificateAt 28 70 5 := by decide +kernel
theorem row_28_70 : ThresholdAt 28 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 70 0 cell_28_70_0
    | exact certificate_sound 28 70 1 cell_28_70_1
    | exact certificate_sound 28 70 2 cell_28_70_2
    | exact certificate_sound 28 70 3 cell_28_70_3
    | exact certificate_sound 28 70 4 cell_28_70_4
    | exact certificate_sound 28 70 5 cell_28_70_5
theorem cell_28_71_0 : CertificateAt 28 71 0 := by decide +kernel
theorem cell_28_71_1 : CertificateAt 28 71 1 := by decide +kernel
theorem cell_28_71_2 : CertificateAt 28 71 2 := by decide +kernel
theorem cell_28_71_3 : CertificateAt 28 71 3 := by decide +kernel
theorem cell_28_71_4 : CertificateAt 28 71 4 := by decide +kernel
theorem cell_28_71_5 : CertificateAt 28 71 5 := by decide +kernel
theorem row_28_71 : ThresholdAt 28 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 71 0 cell_28_71_0
    | exact certificate_sound 28 71 1 cell_28_71_1
    | exact certificate_sound 28 71 2 cell_28_71_2
    | exact certificate_sound 28 71 3 cell_28_71_3
    | exact certificate_sound 28 71 4 cell_28_71_4
    | exact certificate_sound 28 71 5 cell_28_71_5
theorem cell_28_72_0 : CertificateAt 28 72 0 := by decide +kernel
theorem cell_28_72_1 : CertificateAt 28 72 1 := by decide +kernel
theorem cell_28_72_2 : CertificateAt 28 72 2 := by decide +kernel
theorem cell_28_72_3 : CertificateAt 28 72 3 := by decide +kernel
theorem cell_28_72_4 : CertificateAt 28 72 4 := by decide +kernel
theorem cell_28_72_5 : CertificateAt 28 72 5 := by decide +kernel
theorem row_28_72 : ThresholdAt 28 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 72 0 cell_28_72_0
    | exact certificate_sound 28 72 1 cell_28_72_1
    | exact certificate_sound 28 72 2 cell_28_72_2
    | exact certificate_sound 28 72 3 cell_28_72_3
    | exact certificate_sound 28 72 4 cell_28_72_4
    | exact certificate_sound 28 72 5 cell_28_72_5
theorem cell_28_73_0 : CertificateAt 28 73 0 := by decide +kernel
theorem cell_28_73_1 : CertificateAt 28 73 1 := by decide +kernel
theorem cell_28_73_2 : CertificateAt 28 73 2 := by decide +kernel
theorem cell_28_73_3 : CertificateAt 28 73 3 := by decide +kernel
theorem cell_28_73_4 : CertificateAt 28 73 4 := by decide +kernel
theorem cell_28_73_5 : CertificateAt 28 73 5 := by decide +kernel
theorem row_28_73 : ThresholdAt 28 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 73 0 cell_28_73_0
    | exact certificate_sound 28 73 1 cell_28_73_1
    | exact certificate_sound 28 73 2 cell_28_73_2
    | exact certificate_sound 28 73 3 cell_28_73_3
    | exact certificate_sound 28 73 4 cell_28_73_4
    | exact certificate_sound 28 73 5 cell_28_73_5
theorem cell_28_74_0 : CertificateAt 28 74 0 := by decide +kernel
theorem cell_28_74_1 : CertificateAt 28 74 1 := by decide +kernel
theorem cell_28_74_2 : CertificateAt 28 74 2 := by decide +kernel
theorem cell_28_74_3 : CertificateAt 28 74 3 := by decide +kernel
theorem cell_28_74_4 : CertificateAt 28 74 4 := by decide +kernel
theorem cell_28_74_5 : CertificateAt 28 74 5 := by decide +kernel
theorem row_28_74 : ThresholdAt 28 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 74 0 cell_28_74_0
    | exact certificate_sound 28 74 1 cell_28_74_1
    | exact certificate_sound 28 74 2 cell_28_74_2
    | exact certificate_sound 28 74 3 cell_28_74_3
    | exact certificate_sound 28 74 4 cell_28_74_4
    | exact certificate_sound 28 74 5 cell_28_74_5
theorem cell_28_75_0 : CertificateAt 28 75 0 := by decide +kernel
theorem cell_28_75_1 : CertificateAt 28 75 1 := by decide +kernel
theorem cell_28_75_2 : CertificateAt 28 75 2 := by decide +kernel
theorem cell_28_75_3 : CertificateAt 28 75 3 := by decide +kernel
theorem cell_28_75_4 : CertificateAt 28 75 4 := by decide +kernel
theorem cell_28_75_5 : CertificateAt 28 75 5 := by decide +kernel
theorem row_28_75 : ThresholdAt 28 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 75 0 cell_28_75_0
    | exact certificate_sound 28 75 1 cell_28_75_1
    | exact certificate_sound 28 75 2 cell_28_75_2
    | exact certificate_sound 28 75 3 cell_28_75_3
    | exact certificate_sound 28 75 4 cell_28_75_4
    | exact certificate_sound 28 75 5 cell_28_75_5
theorem cell_28_76_0 : CertificateAt 28 76 0 := by decide +kernel
theorem cell_28_76_1 : CertificateAt 28 76 1 := by decide +kernel
theorem cell_28_76_2 : CertificateAt 28 76 2 := by decide +kernel
theorem cell_28_76_3 : CertificateAt 28 76 3 := by decide +kernel
theorem cell_28_76_4 : CertificateAt 28 76 4 := by decide +kernel
theorem cell_28_76_5 : CertificateAt 28 76 5 := by decide +kernel
theorem row_28_76 : ThresholdAt 28 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 76 0 cell_28_76_0
    | exact certificate_sound 28 76 1 cell_28_76_1
    | exact certificate_sound 28 76 2 cell_28_76_2
    | exact certificate_sound 28 76 3 cell_28_76_3
    | exact certificate_sound 28 76 4 cell_28_76_4
    | exact certificate_sound 28 76 5 cell_28_76_5
theorem cell_28_77_0 : CertificateAt 28 77 0 := by decide +kernel
theorem cell_28_77_1 : CertificateAt 28 77 1 := by decide +kernel
theorem cell_28_77_2 : CertificateAt 28 77 2 := by decide +kernel
theorem cell_28_77_3 : CertificateAt 28 77 3 := by decide +kernel
theorem cell_28_77_4 : CertificateAt 28 77 4 := by decide +kernel
theorem cell_28_77_5 : CertificateAt 28 77 5 := by decide +kernel
theorem row_28_77 : ThresholdAt 28 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 77 0 cell_28_77_0
    | exact certificate_sound 28 77 1 cell_28_77_1
    | exact certificate_sound 28 77 2 cell_28_77_2
    | exact certificate_sound 28 77 3 cell_28_77_3
    | exact certificate_sound 28 77 4 cell_28_77_4
    | exact certificate_sound 28 77 5 cell_28_77_5
theorem cell_28_78_0 : CertificateAt 28 78 0 := by decide +kernel
theorem cell_28_78_1 : CertificateAt 28 78 1 := by decide +kernel
theorem cell_28_78_2 : CertificateAt 28 78 2 := by decide +kernel
theorem cell_28_78_3 : CertificateAt 28 78 3 := by decide +kernel
theorem cell_28_78_4 : CertificateAt 28 78 4 := by decide +kernel
theorem cell_28_78_5 : CertificateAt 28 78 5 := by decide +kernel
theorem row_28_78 : ThresholdAt 28 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 78 0 cell_28_78_0
    | exact certificate_sound 28 78 1 cell_28_78_1
    | exact certificate_sound 28 78 2 cell_28_78_2
    | exact certificate_sound 28 78 3 cell_28_78_3
    | exact certificate_sound 28 78 4 cell_28_78_4
    | exact certificate_sound 28 78 5 cell_28_78_5
theorem cell_28_79_0 : CertificateAt 28 79 0 := by decide +kernel
theorem cell_28_79_1 : CertificateAt 28 79 1 := by decide +kernel
theorem cell_28_79_2 : CertificateAt 28 79 2 := by decide +kernel
theorem cell_28_79_3 : CertificateAt 28 79 3 := by decide +kernel
theorem cell_28_79_4 : CertificateAt 28 79 4 := by decide +kernel
theorem cell_28_79_5 : CertificateAt 28 79 5 := by decide +kernel
theorem row_28_79 : ThresholdAt 28 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 79 0 cell_28_79_0
    | exact certificate_sound 28 79 1 cell_28_79_1
    | exact certificate_sound 28 79 2 cell_28_79_2
    | exact certificate_sound 28 79 3 cell_28_79_3
    | exact certificate_sound 28 79 4 cell_28_79_4
    | exact certificate_sound 28 79 5 cell_28_79_5
theorem cell_28_80_0 : CertificateAt 28 80 0 := by decide +kernel
theorem cell_28_80_1 : CertificateAt 28 80 1 := by decide +kernel
theorem cell_28_80_2 : CertificateAt 28 80 2 := by decide +kernel
theorem cell_28_80_3 : CertificateAt 28 80 3 := by decide +kernel
theorem cell_28_80_4 : CertificateAt 28 80 4 := by decide +kernel
theorem cell_28_80_5 : CertificateAt 28 80 5 := by decide +kernel
theorem row_28_80 : ThresholdAt 28 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 80 0 cell_28_80_0
    | exact certificate_sound 28 80 1 cell_28_80_1
    | exact certificate_sound 28 80 2 cell_28_80_2
    | exact certificate_sound 28 80 3 cell_28_80_3
    | exact certificate_sound 28 80 4 cell_28_80_4
    | exact certificate_sound 28 80 5 cell_28_80_5
theorem cell_28_81_0 : CertificateAt 28 81 0 := by decide +kernel
theorem cell_28_81_1 : CertificateAt 28 81 1 := by decide +kernel
theorem cell_28_81_2 : CertificateAt 28 81 2 := by decide +kernel
theorem cell_28_81_3 : CertificateAt 28 81 3 := by decide +kernel
theorem cell_28_81_4 : CertificateAt 28 81 4 := by decide +kernel
theorem cell_28_81_5 : CertificateAt 28 81 5 := by decide +kernel
theorem row_28_81 : ThresholdAt 28 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 81 0 cell_28_81_0
    | exact certificate_sound 28 81 1 cell_28_81_1
    | exact certificate_sound 28 81 2 cell_28_81_2
    | exact certificate_sound 28 81 3 cell_28_81_3
    | exact certificate_sound 28 81 4 cell_28_81_4
    | exact certificate_sound 28 81 5 cell_28_81_5
theorem cell_28_82_0 : CertificateAt 28 82 0 := by decide +kernel
theorem cell_28_82_1 : CertificateAt 28 82 1 := by decide +kernel
theorem cell_28_82_2 : CertificateAt 28 82 2 := by decide +kernel
theorem cell_28_82_3 : CertificateAt 28 82 3 := by decide +kernel
theorem cell_28_82_4 : CertificateAt 28 82 4 := by decide +kernel
theorem cell_28_82_5 : CertificateAt 28 82 5 := by decide +kernel
theorem row_28_82 : ThresholdAt 28 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 82 0 cell_28_82_0
    | exact certificate_sound 28 82 1 cell_28_82_1
    | exact certificate_sound 28 82 2 cell_28_82_2
    | exact certificate_sound 28 82 3 cell_28_82_3
    | exact certificate_sound 28 82 4 cell_28_82_4
    | exact certificate_sound 28 82 5 cell_28_82_5
theorem cell_28_83_0 : CertificateAt 28 83 0 := by decide +kernel
theorem cell_28_83_1 : CertificateAt 28 83 1 := by decide +kernel
theorem cell_28_83_2 : CertificateAt 28 83 2 := by decide +kernel
theorem cell_28_83_3 : CertificateAt 28 83 3 := by decide +kernel
theorem cell_28_83_4 : CertificateAt 28 83 4 := by decide +kernel
theorem cell_28_83_5 : CertificateAt 28 83 5 := by decide +kernel
theorem row_28_83 : ThresholdAt 28 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 83 0 cell_28_83_0
    | exact certificate_sound 28 83 1 cell_28_83_1
    | exact certificate_sound 28 83 2 cell_28_83_2
    | exact certificate_sound 28 83 3 cell_28_83_3
    | exact certificate_sound 28 83 4 cell_28_83_4
    | exact certificate_sound 28 83 5 cell_28_83_5
theorem cell_28_84_0 : CertificateAt 28 84 0 := by decide +kernel
theorem cell_28_84_1 : CertificateAt 28 84 1 := by decide +kernel
theorem cell_28_84_2 : CertificateAt 28 84 2 := by decide +kernel
theorem cell_28_84_3 : CertificateAt 28 84 3 := by decide +kernel
theorem cell_28_84_4 : CertificateAt 28 84 4 := by decide +kernel
theorem cell_28_84_5 : CertificateAt 28 84 5 := by decide +kernel
theorem row_28_84 : ThresholdAt 28 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 84 0 cell_28_84_0
    | exact certificate_sound 28 84 1 cell_28_84_1
    | exact certificate_sound 28 84 2 cell_28_84_2
    | exact certificate_sound 28 84 3 cell_28_84_3
    | exact certificate_sound 28 84 4 cell_28_84_4
    | exact certificate_sound 28 84 5 cell_28_84_5
theorem cell_28_85_0 : CertificateAt 28 85 0 := by decide +kernel
theorem cell_28_85_1 : CertificateAt 28 85 1 := by decide +kernel
theorem cell_28_85_2 : CertificateAt 28 85 2 := by decide +kernel
theorem cell_28_85_3 : CertificateAt 28 85 3 := by decide +kernel
theorem cell_28_85_4 : CertificateAt 28 85 4 := by decide +kernel
theorem cell_28_85_5 : CertificateAt 28 85 5 := by decide +kernel
theorem row_28_85 : ThresholdAt 28 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 85 0 cell_28_85_0
    | exact certificate_sound 28 85 1 cell_28_85_1
    | exact certificate_sound 28 85 2 cell_28_85_2
    | exact certificate_sound 28 85 3 cell_28_85_3
    | exact certificate_sound 28 85 4 cell_28_85_4
    | exact certificate_sound 28 85 5 cell_28_85_5
theorem cell_28_86_0 : CertificateAt 28 86 0 := by decide +kernel
theorem cell_28_86_1 : CertificateAt 28 86 1 := by decide +kernel
theorem cell_28_86_2 : CertificateAt 28 86 2 := by decide +kernel
theorem cell_28_86_3 : CertificateAt 28 86 3 := by decide +kernel
theorem cell_28_86_4 : CertificateAt 28 86 4 := by decide +kernel
theorem cell_28_86_5 : CertificateAt 28 86 5 := by decide +kernel
theorem row_28_86 : ThresholdAt 28 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 86 0 cell_28_86_0
    | exact certificate_sound 28 86 1 cell_28_86_1
    | exact certificate_sound 28 86 2 cell_28_86_2
    | exact certificate_sound 28 86 3 cell_28_86_3
    | exact certificate_sound 28 86 4 cell_28_86_4
    | exact certificate_sound 28 86 5 cell_28_86_5
theorem cell_28_87_0 : CertificateAt 28 87 0 := by decide +kernel
theorem cell_28_87_1 : CertificateAt 28 87 1 := by decide +kernel
theorem cell_28_87_2 : CertificateAt 28 87 2 := by decide +kernel
theorem cell_28_87_3 : CertificateAt 28 87 3 := by decide +kernel
theorem cell_28_87_4 : CertificateAt 28 87 4 := by decide +kernel
theorem cell_28_87_5 : CertificateAt 28 87 5 := by decide +kernel
theorem row_28_87 : ThresholdAt 28 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 87 0 cell_28_87_0
    | exact certificate_sound 28 87 1 cell_28_87_1
    | exact certificate_sound 28 87 2 cell_28_87_2
    | exact certificate_sound 28 87 3 cell_28_87_3
    | exact certificate_sound 28 87 4 cell_28_87_4
    | exact certificate_sound 28 87 5 cell_28_87_5
theorem cell_28_88_0 : CertificateAt 28 88 0 := by decide +kernel
theorem cell_28_88_1 : CertificateAt 28 88 1 := by decide +kernel
theorem cell_28_88_2 : CertificateAt 28 88 2 := by decide +kernel
theorem cell_28_88_3 : CertificateAt 28 88 3 := by decide +kernel
theorem cell_28_88_4 : CertificateAt 28 88 4 := by decide +kernel
theorem cell_28_88_5 : CertificateAt 28 88 5 := by decide +kernel
theorem row_28_88 : ThresholdAt 28 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 88 0 cell_28_88_0
    | exact certificate_sound 28 88 1 cell_28_88_1
    | exact certificate_sound 28 88 2 cell_28_88_2
    | exact certificate_sound 28 88 3 cell_28_88_3
    | exact certificate_sound 28 88 4 cell_28_88_4
    | exact certificate_sound 28 88 5 cell_28_88_5
theorem cell_28_89_0 : CertificateAt 28 89 0 := by decide +kernel
theorem cell_28_89_1 : CertificateAt 28 89 1 := by decide +kernel
theorem cell_28_89_2 : CertificateAt 28 89 2 := by decide +kernel
theorem cell_28_89_3 : CertificateAt 28 89 3 := by decide +kernel
theorem cell_28_89_4 : CertificateAt 28 89 4 := by decide +kernel
theorem cell_28_89_5 : CertificateAt 28 89 5 := by decide +kernel
theorem row_28_89 : ThresholdAt 28 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 89 0 cell_28_89_0
    | exact certificate_sound 28 89 1 cell_28_89_1
    | exact certificate_sound 28 89 2 cell_28_89_2
    | exact certificate_sound 28 89 3 cell_28_89_3
    | exact certificate_sound 28 89 4 cell_28_89_4
    | exact certificate_sound 28 89 5 cell_28_89_5
theorem cell_28_90_0 : CertificateAt 28 90 0 := by decide +kernel
theorem cell_28_90_1 : CertificateAt 28 90 1 := by decide +kernel
theorem cell_28_90_2 : CertificateAt 28 90 2 := by decide +kernel
theorem cell_28_90_3 : CertificateAt 28 90 3 := by decide +kernel
theorem cell_28_90_4 : CertificateAt 28 90 4 := by decide +kernel
theorem cell_28_90_5 : CertificateAt 28 90 5 := by decide +kernel
theorem row_28_90 : ThresholdAt 28 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 90 0 cell_28_90_0
    | exact certificate_sound 28 90 1 cell_28_90_1
    | exact certificate_sound 28 90 2 cell_28_90_2
    | exact certificate_sound 28 90 3 cell_28_90_3
    | exact certificate_sound 28 90 4 cell_28_90_4
    | exact certificate_sound 28 90 5 cell_28_90_5
theorem cell_28_91_0 : CertificateAt 28 91 0 := by decide +kernel
theorem cell_28_91_1 : CertificateAt 28 91 1 := by decide +kernel
theorem cell_28_91_2 : CertificateAt 28 91 2 := by decide +kernel
theorem cell_28_91_3 : CertificateAt 28 91 3 := by decide +kernel
theorem cell_28_91_4 : CertificateAt 28 91 4 := by decide +kernel
theorem cell_28_91_5 : CertificateAt 28 91 5 := by decide +kernel
theorem row_28_91 : ThresholdAt 28 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 91 0 cell_28_91_0
    | exact certificate_sound 28 91 1 cell_28_91_1
    | exact certificate_sound 28 91 2 cell_28_91_2
    | exact certificate_sound 28 91 3 cell_28_91_3
    | exact certificate_sound 28 91 4 cell_28_91_4
    | exact certificate_sound 28 91 5 cell_28_91_5
theorem cell_28_92_0 : CertificateAt 28 92 0 := by decide +kernel
theorem cell_28_92_1 : CertificateAt 28 92 1 := by decide +kernel
theorem cell_28_92_2 : CertificateAt 28 92 2 := by decide +kernel
theorem cell_28_92_3 : CertificateAt 28 92 3 := by decide +kernel
theorem cell_28_92_4 : CertificateAt 28 92 4 := by decide +kernel
theorem cell_28_92_5 : CertificateAt 28 92 5 := by decide +kernel
theorem row_28_92 : ThresholdAt 28 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 92 0 cell_28_92_0
    | exact certificate_sound 28 92 1 cell_28_92_1
    | exact certificate_sound 28 92 2 cell_28_92_2
    | exact certificate_sound 28 92 3 cell_28_92_3
    | exact certificate_sound 28 92 4 cell_28_92_4
    | exact certificate_sound 28 92 5 cell_28_92_5
theorem cell_28_93_0 : CertificateAt 28 93 0 := by decide +kernel
theorem cell_28_93_1 : CertificateAt 28 93 1 := by decide +kernel
theorem cell_28_93_2 : CertificateAt 28 93 2 := by decide +kernel
theorem cell_28_93_3 : CertificateAt 28 93 3 := by decide +kernel
theorem cell_28_93_4 : CertificateAt 28 93 4 := by decide +kernel
theorem cell_28_93_5 : CertificateAt 28 93 5 := by decide +kernel
theorem row_28_93 : ThresholdAt 28 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 93 0 cell_28_93_0
    | exact certificate_sound 28 93 1 cell_28_93_1
    | exact certificate_sound 28 93 2 cell_28_93_2
    | exact certificate_sound 28 93 3 cell_28_93_3
    | exact certificate_sound 28 93 4 cell_28_93_4
    | exact certificate_sound 28 93 5 cell_28_93_5
theorem cell_28_94_0 : CertificateAt 28 94 0 := by decide +kernel
theorem cell_28_94_1 : CertificateAt 28 94 1 := by decide +kernel
theorem cell_28_94_2 : CertificateAt 28 94 2 := by decide +kernel
theorem cell_28_94_3 : CertificateAt 28 94 3 := by decide +kernel
theorem cell_28_94_4 : CertificateAt 28 94 4 := by decide +kernel
theorem cell_28_94_5 : CertificateAt 28 94 5 := by decide +kernel
theorem row_28_94 : ThresholdAt 28 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 94 0 cell_28_94_0
    | exact certificate_sound 28 94 1 cell_28_94_1
    | exact certificate_sound 28 94 2 cell_28_94_2
    | exact certificate_sound 28 94 3 cell_28_94_3
    | exact certificate_sound 28 94 4 cell_28_94_4
    | exact certificate_sound 28 94 5 cell_28_94_5
theorem cell_28_95_0 : CertificateAt 28 95 0 := by decide +kernel
theorem cell_28_95_1 : CertificateAt 28 95 1 := by decide +kernel
theorem cell_28_95_2 : CertificateAt 28 95 2 := by decide +kernel
theorem cell_28_95_3 : CertificateAt 28 95 3 := by decide +kernel
theorem cell_28_95_4 : CertificateAt 28 95 4 := by decide +kernel
theorem cell_28_95_5 : CertificateAt 28 95 5 := by decide +kernel
theorem row_28_95 : ThresholdAt 28 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 95 0 cell_28_95_0
    | exact certificate_sound 28 95 1 cell_28_95_1
    | exact certificate_sound 28 95 2 cell_28_95_2
    | exact certificate_sound 28 95 3 cell_28_95_3
    | exact certificate_sound 28 95 4 cell_28_95_4
    | exact certificate_sound 28 95 5 cell_28_95_5
theorem cell_28_96_0 : CertificateAt 28 96 0 := by decide +kernel
theorem cell_28_96_1 : CertificateAt 28 96 1 := by decide +kernel
theorem cell_28_96_2 : CertificateAt 28 96 2 := by decide +kernel
theorem cell_28_96_3 : CertificateAt 28 96 3 := by decide +kernel
theorem cell_28_96_4 : CertificateAt 28 96 4 := by decide +kernel
theorem cell_28_96_5 : CertificateAt 28 96 5 := by decide +kernel
theorem row_28_96 : ThresholdAt 28 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 96 0 cell_28_96_0
    | exact certificate_sound 28 96 1 cell_28_96_1
    | exact certificate_sound 28 96 2 cell_28_96_2
    | exact certificate_sound 28 96 3 cell_28_96_3
    | exact certificate_sound 28 96 4 cell_28_96_4
    | exact certificate_sound 28 96 5 cell_28_96_5
theorem cell_28_97_0 : CertificateAt 28 97 0 := by decide +kernel
theorem cell_28_97_1 : CertificateAt 28 97 1 := by decide +kernel
theorem cell_28_97_2 : CertificateAt 28 97 2 := by decide +kernel
theorem cell_28_97_3 : CertificateAt 28 97 3 := by decide +kernel
theorem cell_28_97_4 : CertificateAt 28 97 4 := by decide +kernel
theorem cell_28_97_5 : CertificateAt 28 97 5 := by decide +kernel
theorem row_28_97 : ThresholdAt 28 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 97 0 cell_28_97_0
    | exact certificate_sound 28 97 1 cell_28_97_1
    | exact certificate_sound 28 97 2 cell_28_97_2
    | exact certificate_sound 28 97 3 cell_28_97_3
    | exact certificate_sound 28 97 4 cell_28_97_4
    | exact certificate_sound 28 97 5 cell_28_97_5
theorem cell_28_98_0 : CertificateAt 28 98 0 := by decide +kernel
theorem cell_28_98_1 : CertificateAt 28 98 1 := by decide +kernel
theorem cell_28_98_2 : CertificateAt 28 98 2 := by decide +kernel
theorem cell_28_98_3 : CertificateAt 28 98 3 := by decide +kernel
theorem cell_28_98_4 : CertificateAt 28 98 4 := by decide +kernel
theorem cell_28_98_5 : CertificateAt 28 98 5 := by decide +kernel
theorem row_28_98 : ThresholdAt 28 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 98 0 cell_28_98_0
    | exact certificate_sound 28 98 1 cell_28_98_1
    | exact certificate_sound 28 98 2 cell_28_98_2
    | exact certificate_sound 28 98 3 cell_28_98_3
    | exact certificate_sound 28 98 4 cell_28_98_4
    | exact certificate_sound 28 98 5 cell_28_98_5
theorem cell_28_99_0 : CertificateAt 28 99 0 := by decide +kernel
theorem cell_28_99_1 : CertificateAt 28 99 1 := by decide +kernel
theorem cell_28_99_2 : CertificateAt 28 99 2 := by decide +kernel
theorem cell_28_99_3 : CertificateAt 28 99 3 := by decide +kernel
theorem cell_28_99_4 : CertificateAt 28 99 4 := by decide +kernel
theorem cell_28_99_5 : CertificateAt 28 99 5 := by decide +kernel
theorem row_28_99 : ThresholdAt 28 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 99 0 cell_28_99_0
    | exact certificate_sound 28 99 1 cell_28_99_1
    | exact certificate_sound 28 99 2 cell_28_99_2
    | exact certificate_sound 28 99 3 cell_28_99_3
    | exact certificate_sound 28 99 4 cell_28_99_4
    | exact certificate_sound 28 99 5 cell_28_99_5
theorem cell_28_100_0 : CertificateAt 28 100 0 := by decide +kernel
theorem cell_28_100_1 : CertificateAt 28 100 1 := by decide +kernel
theorem cell_28_100_2 : CertificateAt 28 100 2 := by decide +kernel
theorem cell_28_100_3 : CertificateAt 28 100 3 := by decide +kernel
theorem cell_28_100_4 : CertificateAt 28 100 4 := by decide +kernel
theorem cell_28_100_5 : CertificateAt 28 100 5 := by decide +kernel
theorem row_28_100 : ThresholdAt 28 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 100 0 cell_28_100_0
    | exact certificate_sound 28 100 1 cell_28_100_1
    | exact certificate_sound 28 100 2 cell_28_100_2
    | exact certificate_sound 28 100 3 cell_28_100_3
    | exact certificate_sound 28 100 4 cell_28_100_4
    | exact certificate_sound 28 100 5 cell_28_100_5
theorem cell_28_101_0 : CertificateAt 28 101 0 := by decide +kernel
theorem cell_28_101_1 : CertificateAt 28 101 1 := by decide +kernel
theorem cell_28_101_2 : CertificateAt 28 101 2 := by decide +kernel
theorem cell_28_101_3 : CertificateAt 28 101 3 := by decide +kernel
theorem cell_28_101_4 : CertificateAt 28 101 4 := by decide +kernel
theorem cell_28_101_5 : CertificateAt 28 101 5 := by decide +kernel
theorem row_28_101 : ThresholdAt 28 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 101 0 cell_28_101_0
    | exact certificate_sound 28 101 1 cell_28_101_1
    | exact certificate_sound 28 101 2 cell_28_101_2
    | exact certificate_sound 28 101 3 cell_28_101_3
    | exact certificate_sound 28 101 4 cell_28_101_4
    | exact certificate_sound 28 101 5 cell_28_101_5
theorem cell_28_102_0 : CertificateAt 28 102 0 := by decide +kernel
theorem cell_28_102_1 : CertificateAt 28 102 1 := by decide +kernel
theorem cell_28_102_2 : CertificateAt 28 102 2 := by decide +kernel
theorem cell_28_102_3 : CertificateAt 28 102 3 := by decide +kernel
theorem cell_28_102_4 : CertificateAt 28 102 4 := by decide +kernel
theorem cell_28_102_5 : CertificateAt 28 102 5 := by decide +kernel
theorem row_28_102 : ThresholdAt 28 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 102 0 cell_28_102_0
    | exact certificate_sound 28 102 1 cell_28_102_1
    | exact certificate_sound 28 102 2 cell_28_102_2
    | exact certificate_sound 28 102 3 cell_28_102_3
    | exact certificate_sound 28 102 4 cell_28_102_4
    | exact certificate_sound 28 102 5 cell_28_102_5
theorem cell_28_103_0 : CertificateAt 28 103 0 := by decide +kernel
theorem cell_28_103_1 : CertificateAt 28 103 1 := by decide +kernel
theorem cell_28_103_2 : CertificateAt 28 103 2 := by decide +kernel
theorem cell_28_103_3 : CertificateAt 28 103 3 := by decide +kernel
theorem cell_28_103_4 : CertificateAt 28 103 4 := by decide +kernel
theorem cell_28_103_5 : CertificateAt 28 103 5 := by decide +kernel
theorem row_28_103 : ThresholdAt 28 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 103 0 cell_28_103_0
    | exact certificate_sound 28 103 1 cell_28_103_1
    | exact certificate_sound 28 103 2 cell_28_103_2
    | exact certificate_sound 28 103 3 cell_28_103_3
    | exact certificate_sound 28 103 4 cell_28_103_4
    | exact certificate_sound 28 103 5 cell_28_103_5
theorem cell_28_104_0 : CertificateAt 28 104 0 := by decide +kernel
theorem cell_28_104_1 : CertificateAt 28 104 1 := by decide +kernel
theorem cell_28_104_2 : CertificateAt 28 104 2 := by decide +kernel
theorem cell_28_104_3 : CertificateAt 28 104 3 := by decide +kernel
theorem cell_28_104_4 : CertificateAt 28 104 4 := by decide +kernel
theorem cell_28_104_5 : CertificateAt 28 104 5 := by decide +kernel
theorem row_28_104 : ThresholdAt 28 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 104 0 cell_28_104_0
    | exact certificate_sound 28 104 1 cell_28_104_1
    | exact certificate_sound 28 104 2 cell_28_104_2
    | exact certificate_sound 28 104 3 cell_28_104_3
    | exact certificate_sound 28 104 4 cell_28_104_4
    | exact certificate_sound 28 104 5 cell_28_104_5
theorem cell_28_105_0 : CertificateAt 28 105 0 := by decide +kernel
theorem cell_28_105_1 : CertificateAt 28 105 1 := by decide +kernel
theorem cell_28_105_2 : CertificateAt 28 105 2 := by decide +kernel
theorem cell_28_105_3 : CertificateAt 28 105 3 := by decide +kernel
theorem cell_28_105_4 : CertificateAt 28 105 4 := by decide +kernel
theorem cell_28_105_5 : CertificateAt 28 105 5 := by decide +kernel
theorem row_28_105 : ThresholdAt 28 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 105 0 cell_28_105_0
    | exact certificate_sound 28 105 1 cell_28_105_1
    | exact certificate_sound 28 105 2 cell_28_105_2
    | exact certificate_sound 28 105 3 cell_28_105_3
    | exact certificate_sound 28 105 4 cell_28_105_4
    | exact certificate_sound 28 105 5 cell_28_105_5
theorem cell_28_106_0 : CertificateAt 28 106 0 := by decide +kernel
theorem cell_28_106_1 : CertificateAt 28 106 1 := by decide +kernel
theorem cell_28_106_2 : CertificateAt 28 106 2 := by decide +kernel
theorem cell_28_106_3 : CertificateAt 28 106 3 := by decide +kernel
theorem cell_28_106_4 : CertificateAt 28 106 4 := by decide +kernel
theorem cell_28_106_5 : CertificateAt 28 106 5 := by decide +kernel
theorem row_28_106 : ThresholdAt 28 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 106 0 cell_28_106_0
    | exact certificate_sound 28 106 1 cell_28_106_1
    | exact certificate_sound 28 106 2 cell_28_106_2
    | exact certificate_sound 28 106 3 cell_28_106_3
    | exact certificate_sound 28 106 4 cell_28_106_4
    | exact certificate_sound 28 106 5 cell_28_106_5
theorem cell_28_107_0 : CertificateAt 28 107 0 := by decide +kernel
theorem cell_28_107_1 : CertificateAt 28 107 1 := by decide +kernel
theorem cell_28_107_2 : CertificateAt 28 107 2 := by decide +kernel
theorem cell_28_107_3 : CertificateAt 28 107 3 := by decide +kernel
theorem cell_28_107_4 : CertificateAt 28 107 4 := by decide +kernel
theorem cell_28_107_5 : CertificateAt 28 107 5 := by decide +kernel
theorem row_28_107 : ThresholdAt 28 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 107 0 cell_28_107_0
    | exact certificate_sound 28 107 1 cell_28_107_1
    | exact certificate_sound 28 107 2 cell_28_107_2
    | exact certificate_sound 28 107 3 cell_28_107_3
    | exact certificate_sound 28 107 4 cell_28_107_4
    | exact certificate_sound 28 107 5 cell_28_107_5
theorem cell_28_108_0 : CertificateAt 28 108 0 := by decide +kernel
theorem cell_28_108_1 : CertificateAt 28 108 1 := by decide +kernel
theorem cell_28_108_2 : CertificateAt 28 108 2 := by decide +kernel
theorem cell_28_108_3 : CertificateAt 28 108 3 := by decide +kernel
theorem cell_28_108_4 : CertificateAt 28 108 4 := by decide +kernel
theorem cell_28_108_5 : CertificateAt 28 108 5 := by decide +kernel
theorem row_28_108 : ThresholdAt 28 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 108 0 cell_28_108_0
    | exact certificate_sound 28 108 1 cell_28_108_1
    | exact certificate_sound 28 108 2 cell_28_108_2
    | exact certificate_sound 28 108 3 cell_28_108_3
    | exact certificate_sound 28 108 4 cell_28_108_4
    | exact certificate_sound 28 108 5 cell_28_108_5
theorem cell_28_109_0 : CertificateAt 28 109 0 := by decide +kernel
theorem cell_28_109_1 : CertificateAt 28 109 1 := by decide +kernel
theorem cell_28_109_2 : CertificateAt 28 109 2 := by decide +kernel
theorem cell_28_109_3 : CertificateAt 28 109 3 := by decide +kernel
theorem cell_28_109_4 : CertificateAt 28 109 4 := by decide +kernel
theorem cell_28_109_5 : CertificateAt 28 109 5 := by decide +kernel
theorem row_28_109 : ThresholdAt 28 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 109 0 cell_28_109_0
    | exact certificate_sound 28 109 1 cell_28_109_1
    | exact certificate_sound 28 109 2 cell_28_109_2
    | exact certificate_sound 28 109 3 cell_28_109_3
    | exact certificate_sound 28 109 4 cell_28_109_4
    | exact certificate_sound 28 109 5 cell_28_109_5
theorem cell_28_110_0 : CertificateAt 28 110 0 := by decide +kernel
theorem cell_28_110_1 : CertificateAt 28 110 1 := by decide +kernel
theorem cell_28_110_2 : CertificateAt 28 110 2 := by decide +kernel
theorem cell_28_110_3 : CertificateAt 28 110 3 := by decide +kernel
theorem cell_28_110_4 : CertificateAt 28 110 4 := by decide +kernel
theorem cell_28_110_5 : CertificateAt 28 110 5 := by decide +kernel
theorem row_28_110 : ThresholdAt 28 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 110 0 cell_28_110_0
    | exact certificate_sound 28 110 1 cell_28_110_1
    | exact certificate_sound 28 110 2 cell_28_110_2
    | exact certificate_sound 28 110 3 cell_28_110_3
    | exact certificate_sound 28 110 4 cell_28_110_4
    | exact certificate_sound 28 110 5 cell_28_110_5
theorem cell_28_111_0 : CertificateAt 28 111 0 := by decide +kernel
theorem cell_28_111_1 : CertificateAt 28 111 1 := by decide +kernel
theorem cell_28_111_2 : CertificateAt 28 111 2 := by decide +kernel
theorem cell_28_111_3 : CertificateAt 28 111 3 := by decide +kernel
theorem cell_28_111_4 : CertificateAt 28 111 4 := by decide +kernel
theorem cell_28_111_5 : CertificateAt 28 111 5 := by decide +kernel
theorem row_28_111 : ThresholdAt 28 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 28 111 0 cell_28_111_0
    | exact certificate_sound 28 111 1 cell_28_111_1
    | exact certificate_sound 28 111 2 cell_28_111_2
    | exact certificate_sound 28 111 3 cell_28_111_3
    | exact certificate_sound 28 111 4 cell_28_111_4
    | exact certificate_sound 28 111 5 cell_28_111_5
theorem checkedR28 : ∀ V ∈ List.range 112, ThresholdAt 28 V := by
  intro V hV
  have hv : V < 112 := List.mem_range.mp hV
  by_cases h0_112 : V < 56
  · by_cases h0_56 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_28_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_28_1
              · have he : V = 2 := by omega
                subst V
                exact row_28_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_28_3
              · have he : V = 4 := by omega
                subst V
                exact row_28_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_28_5
              · have he : V = 6 := by omega
                subst V
                exact row_28_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_28_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_28_8
              · have he : V = 9 := by omega
                subst V
                exact row_28_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_28_10
              · have he : V = 11 := by omega
                subst V
                exact row_28_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_28_12
              · have he : V = 13 := by omega
                subst V
                exact row_28_13
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_28_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_28_15
              · have he : V = 16 := by omega
                subst V
                exact row_28_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_28_17
              · have he : V = 18 := by omega
                subst V
                exact row_28_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_28_19
              · have he : V = 20 := by omega
                subst V
                exact row_28_20
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have he : V = 21 := by omega
              subst V
              exact row_28_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_28_22
              · have he : V = 23 := by omega
                subst V
                exact row_28_23
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_28_24
              · have he : V = 25 := by omega
                subst V
                exact row_28_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_28_26
              · have he : V = 27 := by omega
                subst V
                exact row_28_27
    · by_cases h28_56 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have he : V = 28 := by omega
              subst V
              exact row_28_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_28_29
              · have he : V = 30 := by omega
                subst V
                exact row_28_30
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_28_31
              · have he : V = 32 := by omega
                subst V
                exact row_28_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_28_33
              · have he : V = 34 := by omega
                subst V
                exact row_28_34
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have he : V = 35 := by omega
              subst V
              exact row_28_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_28_36
              · have he : V = 37 := by omega
                subst V
                exact row_28_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_28_38
              · have he : V = 39 := by omega
                subst V
                exact row_28_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_28_40
              · have he : V = 41 := by omega
                subst V
                exact row_28_41
      · by_cases h42_56 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have he : V = 42 := by omega
              subst V
              exact row_28_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_28_43
              · have he : V = 44 := by omega
                subst V
                exact row_28_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_28_45
              · have he : V = 46 := by omega
                subst V
                exact row_28_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_28_47
              · have he : V = 48 := by omega
                subst V
                exact row_28_48
        · by_cases h49_56 : V < 52
          · by_cases h49_52 : V < 50
            · have he : V = 49 := by omega
              subst V
              exact row_28_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_28_50
              · have he : V = 51 := by omega
                subst V
                exact row_28_51
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_28_52
              · have he : V = 53 := by omega
                subst V
                exact row_28_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_28_54
              · have he : V = 55 := by omega
                subst V
                exact row_28_55
  · by_cases h56_112 : V < 84
    · by_cases h56_84 : V < 70
      · by_cases h56_70 : V < 63
        · by_cases h56_63 : V < 59
          · by_cases h56_59 : V < 57
            · have he : V = 56 := by omega
              subst V
              exact row_28_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_28_57
              · have he : V = 58 := by omega
                subst V
                exact row_28_58
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_28_59
              · have he : V = 60 := by omega
                subst V
                exact row_28_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_28_61
              · have he : V = 62 := by omega
                subst V
                exact row_28_62
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have he : V = 63 := by omega
              subst V
              exact row_28_63
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_28_64
              · have he : V = 65 := by omega
                subst V
                exact row_28_65
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_28_66
              · have he : V = 67 := by omega
                subst V
                exact row_28_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_28_68
              · have he : V = 69 := by omega
                subst V
                exact row_28_69
      · by_cases h70_84 : V < 77
        · by_cases h70_77 : V < 73
          · by_cases h70_73 : V < 71
            · have he : V = 70 := by omega
              subst V
              exact row_28_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_28_71
              · have he : V = 72 := by omega
                subst V
                exact row_28_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_28_73
              · have he : V = 74 := by omega
                subst V
                exact row_28_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_28_75
              · have he : V = 76 := by omega
                subst V
                exact row_28_76
        · by_cases h77_84 : V < 80
          · by_cases h77_80 : V < 78
            · have he : V = 77 := by omega
              subst V
              exact row_28_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_28_78
              · have he : V = 79 := by omega
                subst V
                exact row_28_79
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_28_80
              · have he : V = 81 := by omega
                subst V
                exact row_28_81
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_28_82
              · have he : V = 83 := by omega
                subst V
                exact row_28_83
    · by_cases h84_112 : V < 98
      · by_cases h84_98 : V < 91
        · by_cases h84_91 : V < 87
          · by_cases h84_87 : V < 85
            · have he : V = 84 := by omega
              subst V
              exact row_28_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_28_85
              · have he : V = 86 := by omega
                subst V
                exact row_28_86
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_28_87
              · have he : V = 88 := by omega
                subst V
                exact row_28_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_28_89
              · have he : V = 90 := by omega
                subst V
                exact row_28_90
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have he : V = 91 := by omega
              subst V
              exact row_28_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_28_92
              · have he : V = 93 := by omega
                subst V
                exact row_28_93
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_28_94
              · have he : V = 95 := by omega
                subst V
                exact row_28_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_28_96
              · have he : V = 97 := by omega
                subst V
                exact row_28_97
      · by_cases h98_112 : V < 105
        · by_cases h98_105 : V < 101
          · by_cases h98_101 : V < 99
            · have he : V = 98 := by omega
              subst V
              exact row_28_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_28_99
              · have he : V = 100 := by omega
                subst V
                exact row_28_100
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_28_101
              · have he : V = 102 := by omega
                subst V
                exact row_28_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_28_103
              · have he : V = 104 := by omega
                subst V
                exact row_28_104
        · by_cases h105_112 : V < 108
          · by_cases h105_108 : V < 106
            · have he : V = 105 := by omega
              subst V
              exact row_28_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_28_106
              · have he : V = 107 := by omega
                subst V
                exact row_28_107
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_28_108
              · have he : V = 109 := by omega
                subst V
                exact row_28_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_28_110
              · have he : V = 111 := by omega
                subst V
                exact row_28_111
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
