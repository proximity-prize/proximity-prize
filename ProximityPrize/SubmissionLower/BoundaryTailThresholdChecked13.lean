import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked12

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_13_0_0 : CertificateAt 13 0 0 := by decide +kernel
theorem cell_13_0_1 : CertificateAt 13 0 1 := by decide +kernel
theorem cell_13_0_2 : CertificateAt 13 0 2 := by decide +kernel
theorem cell_13_0_3 : CertificateAt 13 0 3 := by decide +kernel
theorem cell_13_0_4 : CertificateAt 13 0 4 := by decide +kernel
theorem cell_13_0_5 : CertificateAt 13 0 5 := by decide +kernel
theorem row_13_0 : ThresholdAt 13 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 0 0 cell_13_0_0
    | exact certificate_sound 13 0 1 cell_13_0_1
    | exact certificate_sound 13 0 2 cell_13_0_2
    | exact certificate_sound 13 0 3 cell_13_0_3
    | exact certificate_sound 13 0 4 cell_13_0_4
    | exact certificate_sound 13 0 5 cell_13_0_5
theorem cell_13_1_0 : CertificateAt 13 1 0 := by decide +kernel
theorem cell_13_1_1 : CertificateAt 13 1 1 := by decide +kernel
theorem cell_13_1_2 : CertificateAt 13 1 2 := by decide +kernel
theorem cell_13_1_3 : CertificateAt 13 1 3 := by decide +kernel
theorem cell_13_1_4 : CertificateAt 13 1 4 := by decide +kernel
theorem cell_13_1_5 : CertificateAt 13 1 5 := by decide +kernel
theorem row_13_1 : ThresholdAt 13 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 1 0 cell_13_1_0
    | exact certificate_sound 13 1 1 cell_13_1_1
    | exact certificate_sound 13 1 2 cell_13_1_2
    | exact certificate_sound 13 1 3 cell_13_1_3
    | exact certificate_sound 13 1 4 cell_13_1_4
    | exact certificate_sound 13 1 5 cell_13_1_5
theorem cell_13_2_0 : CertificateAt 13 2 0 := by decide +kernel
theorem cell_13_2_1 : CertificateAt 13 2 1 := by decide +kernel
theorem cell_13_2_2 : CertificateAt 13 2 2 := by decide +kernel
theorem cell_13_2_3 : CertificateAt 13 2 3 := by decide +kernel
theorem cell_13_2_4 : CertificateAt 13 2 4 := by decide +kernel
theorem cell_13_2_5 : CertificateAt 13 2 5 := by decide +kernel
theorem row_13_2 : ThresholdAt 13 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 2 0 cell_13_2_0
    | exact certificate_sound 13 2 1 cell_13_2_1
    | exact certificate_sound 13 2 2 cell_13_2_2
    | exact certificate_sound 13 2 3 cell_13_2_3
    | exact certificate_sound 13 2 4 cell_13_2_4
    | exact certificate_sound 13 2 5 cell_13_2_5
theorem cell_13_3_0 : CertificateAt 13 3 0 := by decide +kernel
theorem cell_13_3_1 : CertificateAt 13 3 1 := by decide +kernel
theorem cell_13_3_2 : CertificateAt 13 3 2 := by decide +kernel
theorem cell_13_3_3 : CertificateAt 13 3 3 := by decide +kernel
theorem cell_13_3_4 : CertificateAt 13 3 4 := by decide +kernel
theorem cell_13_3_5 : CertificateAt 13 3 5 := by decide +kernel
theorem row_13_3 : ThresholdAt 13 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 3 0 cell_13_3_0
    | exact certificate_sound 13 3 1 cell_13_3_1
    | exact certificate_sound 13 3 2 cell_13_3_2
    | exact certificate_sound 13 3 3 cell_13_3_3
    | exact certificate_sound 13 3 4 cell_13_3_4
    | exact certificate_sound 13 3 5 cell_13_3_5
theorem cell_13_4_0 : CertificateAt 13 4 0 := by decide +kernel
theorem cell_13_4_1 : CertificateAt 13 4 1 := by decide +kernel
theorem cell_13_4_2 : CertificateAt 13 4 2 := by decide +kernel
theorem cell_13_4_3 : CertificateAt 13 4 3 := by decide +kernel
theorem cell_13_4_4 : CertificateAt 13 4 4 := by decide +kernel
theorem cell_13_4_5 : CertificateAt 13 4 5 := by decide +kernel
theorem row_13_4 : ThresholdAt 13 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 4 0 cell_13_4_0
    | exact certificate_sound 13 4 1 cell_13_4_1
    | exact certificate_sound 13 4 2 cell_13_4_2
    | exact certificate_sound 13 4 3 cell_13_4_3
    | exact certificate_sound 13 4 4 cell_13_4_4
    | exact certificate_sound 13 4 5 cell_13_4_5
theorem cell_13_5_0 : CertificateAt 13 5 0 := by decide +kernel
theorem cell_13_5_1 : CertificateAt 13 5 1 := by decide +kernel
theorem cell_13_5_2 : CertificateAt 13 5 2 := by decide +kernel
theorem cell_13_5_3 : CertificateAt 13 5 3 := by decide +kernel
theorem cell_13_5_4 : CertificateAt 13 5 4 := by decide +kernel
theorem cell_13_5_5 : CertificateAt 13 5 5 := by decide +kernel
theorem row_13_5 : ThresholdAt 13 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 5 0 cell_13_5_0
    | exact certificate_sound 13 5 1 cell_13_5_1
    | exact certificate_sound 13 5 2 cell_13_5_2
    | exact certificate_sound 13 5 3 cell_13_5_3
    | exact certificate_sound 13 5 4 cell_13_5_4
    | exact certificate_sound 13 5 5 cell_13_5_5
theorem cell_13_6_0 : CertificateAt 13 6 0 := by decide +kernel
theorem cell_13_6_1 : CertificateAt 13 6 1 := by decide +kernel
theorem cell_13_6_2 : CertificateAt 13 6 2 := by decide +kernel
theorem cell_13_6_3 : CertificateAt 13 6 3 := by decide +kernel
theorem cell_13_6_4 : CertificateAt 13 6 4 := by decide +kernel
theorem cell_13_6_5 : CertificateAt 13 6 5 := by decide +kernel
theorem row_13_6 : ThresholdAt 13 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 6 0 cell_13_6_0
    | exact certificate_sound 13 6 1 cell_13_6_1
    | exact certificate_sound 13 6 2 cell_13_6_2
    | exact certificate_sound 13 6 3 cell_13_6_3
    | exact certificate_sound 13 6 4 cell_13_6_4
    | exact certificate_sound 13 6 5 cell_13_6_5
theorem cell_13_7_0 : CertificateAt 13 7 0 := by decide +kernel
theorem cell_13_7_1 : CertificateAt 13 7 1 := by decide +kernel
theorem cell_13_7_2 : CertificateAt 13 7 2 := by decide +kernel
theorem cell_13_7_3 : CertificateAt 13 7 3 := by decide +kernel
theorem cell_13_7_4 : CertificateAt 13 7 4 := by decide +kernel
theorem cell_13_7_5 : CertificateAt 13 7 5 := by decide +kernel
theorem row_13_7 : ThresholdAt 13 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 7 0 cell_13_7_0
    | exact certificate_sound 13 7 1 cell_13_7_1
    | exact certificate_sound 13 7 2 cell_13_7_2
    | exact certificate_sound 13 7 3 cell_13_7_3
    | exact certificate_sound 13 7 4 cell_13_7_4
    | exact certificate_sound 13 7 5 cell_13_7_5
theorem cell_13_8_0 : CertificateAt 13 8 0 := by decide +kernel
theorem cell_13_8_1 : CertificateAt 13 8 1 := by decide +kernel
theorem cell_13_8_2 : CertificateAt 13 8 2 := by decide +kernel
theorem cell_13_8_3 : CertificateAt 13 8 3 := by decide +kernel
theorem cell_13_8_4 : CertificateAt 13 8 4 := by decide +kernel
theorem cell_13_8_5 : CertificateAt 13 8 5 := by decide +kernel
theorem row_13_8 : ThresholdAt 13 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 8 0 cell_13_8_0
    | exact certificate_sound 13 8 1 cell_13_8_1
    | exact certificate_sound 13 8 2 cell_13_8_2
    | exact certificate_sound 13 8 3 cell_13_8_3
    | exact certificate_sound 13 8 4 cell_13_8_4
    | exact certificate_sound 13 8 5 cell_13_8_5
theorem cell_13_9_0 : CertificateAt 13 9 0 := by decide +kernel
theorem cell_13_9_1 : CertificateAt 13 9 1 := by decide +kernel
theorem cell_13_9_2 : CertificateAt 13 9 2 := by decide +kernel
theorem cell_13_9_3 : CertificateAt 13 9 3 := by decide +kernel
theorem cell_13_9_4 : CertificateAt 13 9 4 := by decide +kernel
theorem cell_13_9_5 : CertificateAt 13 9 5 := by decide +kernel
theorem row_13_9 : ThresholdAt 13 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 9 0 cell_13_9_0
    | exact certificate_sound 13 9 1 cell_13_9_1
    | exact certificate_sound 13 9 2 cell_13_9_2
    | exact certificate_sound 13 9 3 cell_13_9_3
    | exact certificate_sound 13 9 4 cell_13_9_4
    | exact certificate_sound 13 9 5 cell_13_9_5
theorem cell_13_10_0 : CertificateAt 13 10 0 := by decide +kernel
theorem cell_13_10_1 : CertificateAt 13 10 1 := by decide +kernel
theorem cell_13_10_2 : CertificateAt 13 10 2 := by decide +kernel
theorem cell_13_10_3 : CertificateAt 13 10 3 := by decide +kernel
theorem cell_13_10_4 : CertificateAt 13 10 4 := by decide +kernel
theorem cell_13_10_5 : CertificateAt 13 10 5 := by decide +kernel
theorem row_13_10 : ThresholdAt 13 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 10 0 cell_13_10_0
    | exact certificate_sound 13 10 1 cell_13_10_1
    | exact certificate_sound 13 10 2 cell_13_10_2
    | exact certificate_sound 13 10 3 cell_13_10_3
    | exact certificate_sound 13 10 4 cell_13_10_4
    | exact certificate_sound 13 10 5 cell_13_10_5
theorem cell_13_11_0 : CertificateAt 13 11 0 := by decide +kernel
theorem cell_13_11_1 : CertificateAt 13 11 1 := by decide +kernel
theorem cell_13_11_2 : CertificateAt 13 11 2 := by decide +kernel
theorem cell_13_11_3 : CertificateAt 13 11 3 := by decide +kernel
theorem cell_13_11_4 : CertificateAt 13 11 4 := by decide +kernel
theorem cell_13_11_5 : CertificateAt 13 11 5 := by decide +kernel
theorem row_13_11 : ThresholdAt 13 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 11 0 cell_13_11_0
    | exact certificate_sound 13 11 1 cell_13_11_1
    | exact certificate_sound 13 11 2 cell_13_11_2
    | exact certificate_sound 13 11 3 cell_13_11_3
    | exact certificate_sound 13 11 4 cell_13_11_4
    | exact certificate_sound 13 11 5 cell_13_11_5
theorem cell_13_12_0 : CertificateAt 13 12 0 := by decide +kernel
theorem cell_13_12_1 : CertificateAt 13 12 1 := by decide +kernel
theorem cell_13_12_2 : CertificateAt 13 12 2 := by decide +kernel
theorem cell_13_12_3 : CertificateAt 13 12 3 := by decide +kernel
theorem cell_13_12_4 : CertificateAt 13 12 4 := by decide +kernel
theorem cell_13_12_5 : CertificateAt 13 12 5 := by decide +kernel
theorem row_13_12 : ThresholdAt 13 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 12 0 cell_13_12_0
    | exact certificate_sound 13 12 1 cell_13_12_1
    | exact certificate_sound 13 12 2 cell_13_12_2
    | exact certificate_sound 13 12 3 cell_13_12_3
    | exact certificate_sound 13 12 4 cell_13_12_4
    | exact certificate_sound 13 12 5 cell_13_12_5
theorem cell_13_13_0 : CertificateAt 13 13 0 := by decide +kernel
theorem cell_13_13_1 : CertificateAt 13 13 1 := by decide +kernel
theorem cell_13_13_2 : CertificateAt 13 13 2 := by decide +kernel
theorem cell_13_13_3 : CertificateAt 13 13 3 := by decide +kernel
theorem cell_13_13_4 : CertificateAt 13 13 4 := by decide +kernel
theorem cell_13_13_5 : CertificateAt 13 13 5 := by decide +kernel
theorem row_13_13 : ThresholdAt 13 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 13 0 cell_13_13_0
    | exact certificate_sound 13 13 1 cell_13_13_1
    | exact certificate_sound 13 13 2 cell_13_13_2
    | exact certificate_sound 13 13 3 cell_13_13_3
    | exact certificate_sound 13 13 4 cell_13_13_4
    | exact certificate_sound 13 13 5 cell_13_13_5
theorem cell_13_14_0 : CertificateAt 13 14 0 := by decide +kernel
theorem cell_13_14_1 : CertificateAt 13 14 1 := by decide +kernel
theorem cell_13_14_2 : CertificateAt 13 14 2 := by decide +kernel
theorem cell_13_14_3 : CertificateAt 13 14 3 := by decide +kernel
theorem cell_13_14_4 : CertificateAt 13 14 4 := by decide +kernel
theorem cell_13_14_5 : CertificateAt 13 14 5 := by decide +kernel
theorem row_13_14 : ThresholdAt 13 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 14 0 cell_13_14_0
    | exact certificate_sound 13 14 1 cell_13_14_1
    | exact certificate_sound 13 14 2 cell_13_14_2
    | exact certificate_sound 13 14 3 cell_13_14_3
    | exact certificate_sound 13 14 4 cell_13_14_4
    | exact certificate_sound 13 14 5 cell_13_14_5
theorem cell_13_15_0 : CertificateAt 13 15 0 := by decide +kernel
theorem cell_13_15_1 : CertificateAt 13 15 1 := by decide +kernel
theorem cell_13_15_2 : CertificateAt 13 15 2 := by decide +kernel
theorem cell_13_15_3 : CertificateAt 13 15 3 := by decide +kernel
theorem cell_13_15_4 : CertificateAt 13 15 4 := by decide +kernel
theorem cell_13_15_5 : CertificateAt 13 15 5 := by decide +kernel
theorem row_13_15 : ThresholdAt 13 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 15 0 cell_13_15_0
    | exact certificate_sound 13 15 1 cell_13_15_1
    | exact certificate_sound 13 15 2 cell_13_15_2
    | exact certificate_sound 13 15 3 cell_13_15_3
    | exact certificate_sound 13 15 4 cell_13_15_4
    | exact certificate_sound 13 15 5 cell_13_15_5
theorem cell_13_16_0 : CertificateAt 13 16 0 := by decide +kernel
theorem cell_13_16_1 : CertificateAt 13 16 1 := by decide +kernel
theorem cell_13_16_2 : CertificateAt 13 16 2 := by decide +kernel
theorem cell_13_16_3 : CertificateAt 13 16 3 := by decide +kernel
theorem cell_13_16_4 : CertificateAt 13 16 4 := by decide +kernel
theorem cell_13_16_5 : CertificateAt 13 16 5 := by decide +kernel
theorem row_13_16 : ThresholdAt 13 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 16 0 cell_13_16_0
    | exact certificate_sound 13 16 1 cell_13_16_1
    | exact certificate_sound 13 16 2 cell_13_16_2
    | exact certificate_sound 13 16 3 cell_13_16_3
    | exact certificate_sound 13 16 4 cell_13_16_4
    | exact certificate_sound 13 16 5 cell_13_16_5
theorem cell_13_17_0 : CertificateAt 13 17 0 := by decide +kernel
theorem cell_13_17_1 : CertificateAt 13 17 1 := by decide +kernel
theorem cell_13_17_2 : CertificateAt 13 17 2 := by decide +kernel
theorem cell_13_17_3 : CertificateAt 13 17 3 := by decide +kernel
theorem cell_13_17_4 : CertificateAt 13 17 4 := by decide +kernel
theorem cell_13_17_5 : CertificateAt 13 17 5 := by decide +kernel
theorem row_13_17 : ThresholdAt 13 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 17 0 cell_13_17_0
    | exact certificate_sound 13 17 1 cell_13_17_1
    | exact certificate_sound 13 17 2 cell_13_17_2
    | exact certificate_sound 13 17 3 cell_13_17_3
    | exact certificate_sound 13 17 4 cell_13_17_4
    | exact certificate_sound 13 17 5 cell_13_17_5
theorem cell_13_18_0 : CertificateAt 13 18 0 := by decide +kernel
theorem cell_13_18_1 : CertificateAt 13 18 1 := by decide +kernel
theorem cell_13_18_2 : CertificateAt 13 18 2 := by decide +kernel
theorem cell_13_18_3 : CertificateAt 13 18 3 := by decide +kernel
theorem cell_13_18_4 : CertificateAt 13 18 4 := by decide +kernel
theorem cell_13_18_5 : CertificateAt 13 18 5 := by decide +kernel
theorem row_13_18 : ThresholdAt 13 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 18 0 cell_13_18_0
    | exact certificate_sound 13 18 1 cell_13_18_1
    | exact certificate_sound 13 18 2 cell_13_18_2
    | exact certificate_sound 13 18 3 cell_13_18_3
    | exact certificate_sound 13 18 4 cell_13_18_4
    | exact certificate_sound 13 18 5 cell_13_18_5
theorem cell_13_19_0 : CertificateAt 13 19 0 := by decide +kernel
theorem cell_13_19_1 : CertificateAt 13 19 1 := by decide +kernel
theorem cell_13_19_2 : CertificateAt 13 19 2 := by decide +kernel
theorem cell_13_19_3 : CertificateAt 13 19 3 := by decide +kernel
theorem cell_13_19_4 : CertificateAt 13 19 4 := by decide +kernel
theorem cell_13_19_5 : CertificateAt 13 19 5 := by decide +kernel
theorem row_13_19 : ThresholdAt 13 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 19 0 cell_13_19_0
    | exact certificate_sound 13 19 1 cell_13_19_1
    | exact certificate_sound 13 19 2 cell_13_19_2
    | exact certificate_sound 13 19 3 cell_13_19_3
    | exact certificate_sound 13 19 4 cell_13_19_4
    | exact certificate_sound 13 19 5 cell_13_19_5
theorem cell_13_20_0 : CertificateAt 13 20 0 := by decide +kernel
theorem cell_13_20_1 : CertificateAt 13 20 1 := by decide +kernel
theorem cell_13_20_2 : CertificateAt 13 20 2 := by decide +kernel
theorem cell_13_20_3 : CertificateAt 13 20 3 := by decide +kernel
theorem cell_13_20_4 : CertificateAt 13 20 4 := by decide +kernel
theorem cell_13_20_5 : CertificateAt 13 20 5 := by decide +kernel
theorem row_13_20 : ThresholdAt 13 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 20 0 cell_13_20_0
    | exact certificate_sound 13 20 1 cell_13_20_1
    | exact certificate_sound 13 20 2 cell_13_20_2
    | exact certificate_sound 13 20 3 cell_13_20_3
    | exact certificate_sound 13 20 4 cell_13_20_4
    | exact certificate_sound 13 20 5 cell_13_20_5
theorem cell_13_21_0 : CertificateAt 13 21 0 := by decide +kernel
theorem cell_13_21_1 : CertificateAt 13 21 1 := by decide +kernel
theorem cell_13_21_2 : CertificateAt 13 21 2 := by decide +kernel
theorem cell_13_21_3 : CertificateAt 13 21 3 := by decide +kernel
theorem cell_13_21_4 : CertificateAt 13 21 4 := by decide +kernel
theorem cell_13_21_5 : CertificateAt 13 21 5 := by decide +kernel
theorem row_13_21 : ThresholdAt 13 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 21 0 cell_13_21_0
    | exact certificate_sound 13 21 1 cell_13_21_1
    | exact certificate_sound 13 21 2 cell_13_21_2
    | exact certificate_sound 13 21 3 cell_13_21_3
    | exact certificate_sound 13 21 4 cell_13_21_4
    | exact certificate_sound 13 21 5 cell_13_21_5
theorem cell_13_22_0 : CertificateAt 13 22 0 := by decide +kernel
theorem cell_13_22_1 : CertificateAt 13 22 1 := by decide +kernel
theorem cell_13_22_2 : CertificateAt 13 22 2 := by decide +kernel
theorem cell_13_22_3 : CertificateAt 13 22 3 := by decide +kernel
theorem cell_13_22_4 : CertificateAt 13 22 4 := by decide +kernel
theorem cell_13_22_5 : CertificateAt 13 22 5 := by decide +kernel
theorem row_13_22 : ThresholdAt 13 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 22 0 cell_13_22_0
    | exact certificate_sound 13 22 1 cell_13_22_1
    | exact certificate_sound 13 22 2 cell_13_22_2
    | exact certificate_sound 13 22 3 cell_13_22_3
    | exact certificate_sound 13 22 4 cell_13_22_4
    | exact certificate_sound 13 22 5 cell_13_22_5
theorem cell_13_23_0 : CertificateAt 13 23 0 := by decide +kernel
theorem cell_13_23_1 : CertificateAt 13 23 1 := by decide +kernel
theorem cell_13_23_2 : CertificateAt 13 23 2 := by decide +kernel
theorem cell_13_23_3 : CertificateAt 13 23 3 := by decide +kernel
theorem cell_13_23_4 : CertificateAt 13 23 4 := by decide +kernel
theorem cell_13_23_5 : CertificateAt 13 23 5 := by decide +kernel
theorem row_13_23 : ThresholdAt 13 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 23 0 cell_13_23_0
    | exact certificate_sound 13 23 1 cell_13_23_1
    | exact certificate_sound 13 23 2 cell_13_23_2
    | exact certificate_sound 13 23 3 cell_13_23_3
    | exact certificate_sound 13 23 4 cell_13_23_4
    | exact certificate_sound 13 23 5 cell_13_23_5
theorem cell_13_24_0 : CertificateAt 13 24 0 := by decide +kernel
theorem cell_13_24_1 : CertificateAt 13 24 1 := by decide +kernel
theorem cell_13_24_2 : CertificateAt 13 24 2 := by decide +kernel
theorem cell_13_24_3 : CertificateAt 13 24 3 := by decide +kernel
theorem cell_13_24_4 : CertificateAt 13 24 4 := by decide +kernel
theorem cell_13_24_5 : CertificateAt 13 24 5 := by decide +kernel
theorem row_13_24 : ThresholdAt 13 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 24 0 cell_13_24_0
    | exact certificate_sound 13 24 1 cell_13_24_1
    | exact certificate_sound 13 24 2 cell_13_24_2
    | exact certificate_sound 13 24 3 cell_13_24_3
    | exact certificate_sound 13 24 4 cell_13_24_4
    | exact certificate_sound 13 24 5 cell_13_24_5
theorem cell_13_25_0 : CertificateAt 13 25 0 := by decide +kernel
theorem cell_13_25_1 : CertificateAt 13 25 1 := by decide +kernel
theorem cell_13_25_2 : CertificateAt 13 25 2 := by decide +kernel
theorem cell_13_25_3 : CertificateAt 13 25 3 := by decide +kernel
theorem cell_13_25_4 : CertificateAt 13 25 4 := by decide +kernel
theorem cell_13_25_5 : CertificateAt 13 25 5 := by decide +kernel
theorem row_13_25 : ThresholdAt 13 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 25 0 cell_13_25_0
    | exact certificate_sound 13 25 1 cell_13_25_1
    | exact certificate_sound 13 25 2 cell_13_25_2
    | exact certificate_sound 13 25 3 cell_13_25_3
    | exact certificate_sound 13 25 4 cell_13_25_4
    | exact certificate_sound 13 25 5 cell_13_25_5
theorem cell_13_26_0 : CertificateAt 13 26 0 := by decide +kernel
theorem cell_13_26_1 : CertificateAt 13 26 1 := by decide +kernel
theorem cell_13_26_2 : CertificateAt 13 26 2 := by decide +kernel
theorem cell_13_26_3 : CertificateAt 13 26 3 := by decide +kernel
theorem cell_13_26_4 : CertificateAt 13 26 4 := by decide +kernel
theorem cell_13_26_5 : CertificateAt 13 26 5 := by decide +kernel
theorem row_13_26 : ThresholdAt 13 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 26 0 cell_13_26_0
    | exact certificate_sound 13 26 1 cell_13_26_1
    | exact certificate_sound 13 26 2 cell_13_26_2
    | exact certificate_sound 13 26 3 cell_13_26_3
    | exact certificate_sound 13 26 4 cell_13_26_4
    | exact certificate_sound 13 26 5 cell_13_26_5
theorem cell_13_27_0 : CertificateAt 13 27 0 := by decide +kernel
theorem cell_13_27_1 : CertificateAt 13 27 1 := by decide +kernel
theorem cell_13_27_2 : CertificateAt 13 27 2 := by decide +kernel
theorem cell_13_27_3 : CertificateAt 13 27 3 := by decide +kernel
theorem cell_13_27_4 : CertificateAt 13 27 4 := by decide +kernel
theorem cell_13_27_5 : CertificateAt 13 27 5 := by decide +kernel
theorem row_13_27 : ThresholdAt 13 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 27 0 cell_13_27_0
    | exact certificate_sound 13 27 1 cell_13_27_1
    | exact certificate_sound 13 27 2 cell_13_27_2
    | exact certificate_sound 13 27 3 cell_13_27_3
    | exact certificate_sound 13 27 4 cell_13_27_4
    | exact certificate_sound 13 27 5 cell_13_27_5
theorem cell_13_28_0 : CertificateAt 13 28 0 := by decide +kernel
theorem cell_13_28_1 : CertificateAt 13 28 1 := by decide +kernel
theorem cell_13_28_2 : CertificateAt 13 28 2 := by decide +kernel
theorem cell_13_28_3 : CertificateAt 13 28 3 := by decide +kernel
theorem cell_13_28_4 : CertificateAt 13 28 4 := by decide +kernel
theorem cell_13_28_5 : CertificateAt 13 28 5 := by decide +kernel
theorem row_13_28 : ThresholdAt 13 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 28 0 cell_13_28_0
    | exact certificate_sound 13 28 1 cell_13_28_1
    | exact certificate_sound 13 28 2 cell_13_28_2
    | exact certificate_sound 13 28 3 cell_13_28_3
    | exact certificate_sound 13 28 4 cell_13_28_4
    | exact certificate_sound 13 28 5 cell_13_28_5
theorem cell_13_29_0 : CertificateAt 13 29 0 := by decide +kernel
theorem cell_13_29_1 : CertificateAt 13 29 1 := by decide +kernel
theorem cell_13_29_2 : CertificateAt 13 29 2 := by decide +kernel
theorem cell_13_29_3 : CertificateAt 13 29 3 := by decide +kernel
theorem cell_13_29_4 : CertificateAt 13 29 4 := by decide +kernel
theorem cell_13_29_5 : CertificateAt 13 29 5 := by decide +kernel
theorem row_13_29 : ThresholdAt 13 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 29 0 cell_13_29_0
    | exact certificate_sound 13 29 1 cell_13_29_1
    | exact certificate_sound 13 29 2 cell_13_29_2
    | exact certificate_sound 13 29 3 cell_13_29_3
    | exact certificate_sound 13 29 4 cell_13_29_4
    | exact certificate_sound 13 29 5 cell_13_29_5
theorem cell_13_30_0 : CertificateAt 13 30 0 := by decide +kernel
theorem cell_13_30_1 : CertificateAt 13 30 1 := by decide +kernel
theorem cell_13_30_2 : CertificateAt 13 30 2 := by decide +kernel
theorem cell_13_30_3 : CertificateAt 13 30 3 := by decide +kernel
theorem cell_13_30_4 : CertificateAt 13 30 4 := by decide +kernel
theorem cell_13_30_5 : CertificateAt 13 30 5 := by decide +kernel
theorem row_13_30 : ThresholdAt 13 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 30 0 cell_13_30_0
    | exact certificate_sound 13 30 1 cell_13_30_1
    | exact certificate_sound 13 30 2 cell_13_30_2
    | exact certificate_sound 13 30 3 cell_13_30_3
    | exact certificate_sound 13 30 4 cell_13_30_4
    | exact certificate_sound 13 30 5 cell_13_30_5
theorem cell_13_31_0 : CertificateAt 13 31 0 := by decide +kernel
theorem cell_13_31_1 : CertificateAt 13 31 1 := by decide +kernel
theorem cell_13_31_2 : CertificateAt 13 31 2 := by decide +kernel
theorem cell_13_31_3 : CertificateAt 13 31 3 := by decide +kernel
theorem cell_13_31_4 : CertificateAt 13 31 4 := by decide +kernel
theorem cell_13_31_5 : CertificateAt 13 31 5 := by decide +kernel
theorem row_13_31 : ThresholdAt 13 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 31 0 cell_13_31_0
    | exact certificate_sound 13 31 1 cell_13_31_1
    | exact certificate_sound 13 31 2 cell_13_31_2
    | exact certificate_sound 13 31 3 cell_13_31_3
    | exact certificate_sound 13 31 4 cell_13_31_4
    | exact certificate_sound 13 31 5 cell_13_31_5
theorem cell_13_32_0 : CertificateAt 13 32 0 := by decide +kernel
theorem cell_13_32_1 : CertificateAt 13 32 1 := by decide +kernel
theorem cell_13_32_2 : CertificateAt 13 32 2 := by decide +kernel
theorem cell_13_32_3 : CertificateAt 13 32 3 := by decide +kernel
theorem cell_13_32_4 : CertificateAt 13 32 4 := by decide +kernel
theorem cell_13_32_5 : CertificateAt 13 32 5 := by decide +kernel
theorem row_13_32 : ThresholdAt 13 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 32 0 cell_13_32_0
    | exact certificate_sound 13 32 1 cell_13_32_1
    | exact certificate_sound 13 32 2 cell_13_32_2
    | exact certificate_sound 13 32 3 cell_13_32_3
    | exact certificate_sound 13 32 4 cell_13_32_4
    | exact certificate_sound 13 32 5 cell_13_32_5
theorem cell_13_33_0 : CertificateAt 13 33 0 := by decide +kernel
theorem cell_13_33_1 : CertificateAt 13 33 1 := by decide +kernel
theorem cell_13_33_2 : CertificateAt 13 33 2 := by decide +kernel
theorem cell_13_33_3 : CertificateAt 13 33 3 := by decide +kernel
theorem cell_13_33_4 : CertificateAt 13 33 4 := by decide +kernel
theorem cell_13_33_5 : CertificateAt 13 33 5 := by decide +kernel
theorem row_13_33 : ThresholdAt 13 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 33 0 cell_13_33_0
    | exact certificate_sound 13 33 1 cell_13_33_1
    | exact certificate_sound 13 33 2 cell_13_33_2
    | exact certificate_sound 13 33 3 cell_13_33_3
    | exact certificate_sound 13 33 4 cell_13_33_4
    | exact certificate_sound 13 33 5 cell_13_33_5
theorem cell_13_34_0 : CertificateAt 13 34 0 := by decide +kernel
theorem cell_13_34_1 : CertificateAt 13 34 1 := by decide +kernel
theorem cell_13_34_2 : CertificateAt 13 34 2 := by decide +kernel
theorem cell_13_34_3 : CertificateAt 13 34 3 := by decide +kernel
theorem cell_13_34_4 : CertificateAt 13 34 4 := by decide +kernel
theorem cell_13_34_5 : CertificateAt 13 34 5 := by decide +kernel
theorem row_13_34 : ThresholdAt 13 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 34 0 cell_13_34_0
    | exact certificate_sound 13 34 1 cell_13_34_1
    | exact certificate_sound 13 34 2 cell_13_34_2
    | exact certificate_sound 13 34 3 cell_13_34_3
    | exact certificate_sound 13 34 4 cell_13_34_4
    | exact certificate_sound 13 34 5 cell_13_34_5
theorem cell_13_35_0 : CertificateAt 13 35 0 := by decide +kernel
theorem cell_13_35_1 : CertificateAt 13 35 1 := by decide +kernel
theorem cell_13_35_2 : CertificateAt 13 35 2 := by decide +kernel
theorem cell_13_35_3 : CertificateAt 13 35 3 := by decide +kernel
theorem cell_13_35_4 : CertificateAt 13 35 4 := by decide +kernel
theorem cell_13_35_5 : CertificateAt 13 35 5 := by decide +kernel
theorem row_13_35 : ThresholdAt 13 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 35 0 cell_13_35_0
    | exact certificate_sound 13 35 1 cell_13_35_1
    | exact certificate_sound 13 35 2 cell_13_35_2
    | exact certificate_sound 13 35 3 cell_13_35_3
    | exact certificate_sound 13 35 4 cell_13_35_4
    | exact certificate_sound 13 35 5 cell_13_35_5
theorem cell_13_36_0 : CertificateAt 13 36 0 := by decide +kernel
theorem cell_13_36_1 : CertificateAt 13 36 1 := by decide +kernel
theorem cell_13_36_2 : CertificateAt 13 36 2 := by decide +kernel
theorem cell_13_36_3 : CertificateAt 13 36 3 := by decide +kernel
theorem cell_13_36_4 : CertificateAt 13 36 4 := by decide +kernel
theorem cell_13_36_5 : CertificateAt 13 36 5 := by decide +kernel
theorem row_13_36 : ThresholdAt 13 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 36 0 cell_13_36_0
    | exact certificate_sound 13 36 1 cell_13_36_1
    | exact certificate_sound 13 36 2 cell_13_36_2
    | exact certificate_sound 13 36 3 cell_13_36_3
    | exact certificate_sound 13 36 4 cell_13_36_4
    | exact certificate_sound 13 36 5 cell_13_36_5
theorem cell_13_37_0 : CertificateAt 13 37 0 := by decide +kernel
theorem cell_13_37_1 : CertificateAt 13 37 1 := by decide +kernel
theorem cell_13_37_2 : CertificateAt 13 37 2 := by decide +kernel
theorem cell_13_37_3 : CertificateAt 13 37 3 := by decide +kernel
theorem cell_13_37_4 : CertificateAt 13 37 4 := by decide +kernel
theorem cell_13_37_5 : CertificateAt 13 37 5 := by decide +kernel
theorem row_13_37 : ThresholdAt 13 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 37 0 cell_13_37_0
    | exact certificate_sound 13 37 1 cell_13_37_1
    | exact certificate_sound 13 37 2 cell_13_37_2
    | exact certificate_sound 13 37 3 cell_13_37_3
    | exact certificate_sound 13 37 4 cell_13_37_4
    | exact certificate_sound 13 37 5 cell_13_37_5
theorem cell_13_38_0 : CertificateAt 13 38 0 := by decide +kernel
theorem cell_13_38_1 : CertificateAt 13 38 1 := by decide +kernel
theorem cell_13_38_2 : CertificateAt 13 38 2 := by decide +kernel
theorem cell_13_38_3 : CertificateAt 13 38 3 := by decide +kernel
theorem cell_13_38_4 : CertificateAt 13 38 4 := by decide +kernel
theorem cell_13_38_5 : CertificateAt 13 38 5 := by decide +kernel
theorem row_13_38 : ThresholdAt 13 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 38 0 cell_13_38_0
    | exact certificate_sound 13 38 1 cell_13_38_1
    | exact certificate_sound 13 38 2 cell_13_38_2
    | exact certificate_sound 13 38 3 cell_13_38_3
    | exact certificate_sound 13 38 4 cell_13_38_4
    | exact certificate_sound 13 38 5 cell_13_38_5
theorem cell_13_39_0 : CertificateAt 13 39 0 := by decide +kernel
theorem cell_13_39_1 : CertificateAt 13 39 1 := by decide +kernel
theorem cell_13_39_2 : CertificateAt 13 39 2 := by decide +kernel
theorem cell_13_39_3 : CertificateAt 13 39 3 := by decide +kernel
theorem cell_13_39_4 : CertificateAt 13 39 4 := by decide +kernel
theorem cell_13_39_5 : CertificateAt 13 39 5 := by decide +kernel
theorem row_13_39 : ThresholdAt 13 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 39 0 cell_13_39_0
    | exact certificate_sound 13 39 1 cell_13_39_1
    | exact certificate_sound 13 39 2 cell_13_39_2
    | exact certificate_sound 13 39 3 cell_13_39_3
    | exact certificate_sound 13 39 4 cell_13_39_4
    | exact certificate_sound 13 39 5 cell_13_39_5
theorem cell_13_40_0 : CertificateAt 13 40 0 := by decide +kernel
theorem cell_13_40_1 : CertificateAt 13 40 1 := by decide +kernel
theorem cell_13_40_2 : CertificateAt 13 40 2 := by decide +kernel
theorem cell_13_40_3 : CertificateAt 13 40 3 := by decide +kernel
theorem cell_13_40_4 : CertificateAt 13 40 4 := by decide +kernel
theorem cell_13_40_5 : CertificateAt 13 40 5 := by decide +kernel
theorem row_13_40 : ThresholdAt 13 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 40 0 cell_13_40_0
    | exact certificate_sound 13 40 1 cell_13_40_1
    | exact certificate_sound 13 40 2 cell_13_40_2
    | exact certificate_sound 13 40 3 cell_13_40_3
    | exact certificate_sound 13 40 4 cell_13_40_4
    | exact certificate_sound 13 40 5 cell_13_40_5
theorem cell_13_41_0 : CertificateAt 13 41 0 := by decide +kernel
theorem cell_13_41_1 : CertificateAt 13 41 1 := by decide +kernel
theorem cell_13_41_2 : CertificateAt 13 41 2 := by decide +kernel
theorem cell_13_41_3 : CertificateAt 13 41 3 := by decide +kernel
theorem cell_13_41_4 : CertificateAt 13 41 4 := by decide +kernel
theorem cell_13_41_5 : CertificateAt 13 41 5 := by decide +kernel
theorem row_13_41 : ThresholdAt 13 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 41 0 cell_13_41_0
    | exact certificate_sound 13 41 1 cell_13_41_1
    | exact certificate_sound 13 41 2 cell_13_41_2
    | exact certificate_sound 13 41 3 cell_13_41_3
    | exact certificate_sound 13 41 4 cell_13_41_4
    | exact certificate_sound 13 41 5 cell_13_41_5
theorem cell_13_42_0 : CertificateAt 13 42 0 := by decide +kernel
theorem cell_13_42_1 : CertificateAt 13 42 1 := by decide +kernel
theorem cell_13_42_2 : CertificateAt 13 42 2 := by decide +kernel
theorem cell_13_42_3 : CertificateAt 13 42 3 := by decide +kernel
theorem cell_13_42_4 : CertificateAt 13 42 4 := by decide +kernel
theorem cell_13_42_5 : CertificateAt 13 42 5 := by decide +kernel
theorem row_13_42 : ThresholdAt 13 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 42 0 cell_13_42_0
    | exact certificate_sound 13 42 1 cell_13_42_1
    | exact certificate_sound 13 42 2 cell_13_42_2
    | exact certificate_sound 13 42 3 cell_13_42_3
    | exact certificate_sound 13 42 4 cell_13_42_4
    | exact certificate_sound 13 42 5 cell_13_42_5
theorem cell_13_43_0 : CertificateAt 13 43 0 := by decide +kernel
theorem cell_13_43_1 : CertificateAt 13 43 1 := by decide +kernel
theorem cell_13_43_2 : CertificateAt 13 43 2 := by decide +kernel
theorem cell_13_43_3 : CertificateAt 13 43 3 := by decide +kernel
theorem cell_13_43_4 : CertificateAt 13 43 4 := by decide +kernel
theorem cell_13_43_5 : CertificateAt 13 43 5 := by decide +kernel
theorem row_13_43 : ThresholdAt 13 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 43 0 cell_13_43_0
    | exact certificate_sound 13 43 1 cell_13_43_1
    | exact certificate_sound 13 43 2 cell_13_43_2
    | exact certificate_sound 13 43 3 cell_13_43_3
    | exact certificate_sound 13 43 4 cell_13_43_4
    | exact certificate_sound 13 43 5 cell_13_43_5
theorem cell_13_44_0 : CertificateAt 13 44 0 := by decide +kernel
theorem cell_13_44_1 : CertificateAt 13 44 1 := by decide +kernel
theorem cell_13_44_2 : CertificateAt 13 44 2 := by decide +kernel
theorem cell_13_44_3 : CertificateAt 13 44 3 := by decide +kernel
theorem cell_13_44_4 : CertificateAt 13 44 4 := by decide +kernel
theorem cell_13_44_5 : CertificateAt 13 44 5 := by decide +kernel
theorem row_13_44 : ThresholdAt 13 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 44 0 cell_13_44_0
    | exact certificate_sound 13 44 1 cell_13_44_1
    | exact certificate_sound 13 44 2 cell_13_44_2
    | exact certificate_sound 13 44 3 cell_13_44_3
    | exact certificate_sound 13 44 4 cell_13_44_4
    | exact certificate_sound 13 44 5 cell_13_44_5
theorem cell_13_45_0 : CertificateAt 13 45 0 := by decide +kernel
theorem cell_13_45_1 : CertificateAt 13 45 1 := by decide +kernel
theorem cell_13_45_2 : CertificateAt 13 45 2 := by decide +kernel
theorem cell_13_45_3 : CertificateAt 13 45 3 := by decide +kernel
theorem cell_13_45_4 : CertificateAt 13 45 4 := by decide +kernel
theorem cell_13_45_5 : CertificateAt 13 45 5 := by decide +kernel
theorem row_13_45 : ThresholdAt 13 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 45 0 cell_13_45_0
    | exact certificate_sound 13 45 1 cell_13_45_1
    | exact certificate_sound 13 45 2 cell_13_45_2
    | exact certificate_sound 13 45 3 cell_13_45_3
    | exact certificate_sound 13 45 4 cell_13_45_4
    | exact certificate_sound 13 45 5 cell_13_45_5
theorem cell_13_46_0 : CertificateAt 13 46 0 := by decide +kernel
theorem cell_13_46_1 : CertificateAt 13 46 1 := by decide +kernel
theorem cell_13_46_2 : CertificateAt 13 46 2 := by decide +kernel
theorem cell_13_46_3 : CertificateAt 13 46 3 := by decide +kernel
theorem cell_13_46_4 : CertificateAt 13 46 4 := by decide +kernel
theorem cell_13_46_5 : CertificateAt 13 46 5 := by decide +kernel
theorem row_13_46 : ThresholdAt 13 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 46 0 cell_13_46_0
    | exact certificate_sound 13 46 1 cell_13_46_1
    | exact certificate_sound 13 46 2 cell_13_46_2
    | exact certificate_sound 13 46 3 cell_13_46_3
    | exact certificate_sound 13 46 4 cell_13_46_4
    | exact certificate_sound 13 46 5 cell_13_46_5
theorem cell_13_47_0 : CertificateAt 13 47 0 := by decide +kernel
theorem cell_13_47_1 : CertificateAt 13 47 1 := by decide +kernel
theorem cell_13_47_2 : CertificateAt 13 47 2 := by decide +kernel
theorem cell_13_47_3 : CertificateAt 13 47 3 := by decide +kernel
theorem cell_13_47_4 : CertificateAt 13 47 4 := by decide +kernel
theorem cell_13_47_5 : CertificateAt 13 47 5 := by decide +kernel
theorem row_13_47 : ThresholdAt 13 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 47 0 cell_13_47_0
    | exact certificate_sound 13 47 1 cell_13_47_1
    | exact certificate_sound 13 47 2 cell_13_47_2
    | exact certificate_sound 13 47 3 cell_13_47_3
    | exact certificate_sound 13 47 4 cell_13_47_4
    | exact certificate_sound 13 47 5 cell_13_47_5
theorem cell_13_48_0 : CertificateAt 13 48 0 := by decide +kernel
theorem cell_13_48_1 : CertificateAt 13 48 1 := by decide +kernel
theorem cell_13_48_2 : CertificateAt 13 48 2 := by decide +kernel
theorem cell_13_48_3 : CertificateAt 13 48 3 := by decide +kernel
theorem cell_13_48_4 : CertificateAt 13 48 4 := by decide +kernel
theorem cell_13_48_5 : CertificateAt 13 48 5 := by decide +kernel
theorem row_13_48 : ThresholdAt 13 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 48 0 cell_13_48_0
    | exact certificate_sound 13 48 1 cell_13_48_1
    | exact certificate_sound 13 48 2 cell_13_48_2
    | exact certificate_sound 13 48 3 cell_13_48_3
    | exact certificate_sound 13 48 4 cell_13_48_4
    | exact certificate_sound 13 48 5 cell_13_48_5
theorem cell_13_49_0 : CertificateAt 13 49 0 := by decide +kernel
theorem cell_13_49_1 : CertificateAt 13 49 1 := by decide +kernel
theorem cell_13_49_2 : CertificateAt 13 49 2 := by decide +kernel
theorem cell_13_49_3 : CertificateAt 13 49 3 := by decide +kernel
theorem cell_13_49_4 : CertificateAt 13 49 4 := by decide +kernel
theorem cell_13_49_5 : CertificateAt 13 49 5 := by decide +kernel
theorem row_13_49 : ThresholdAt 13 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 49 0 cell_13_49_0
    | exact certificate_sound 13 49 1 cell_13_49_1
    | exact certificate_sound 13 49 2 cell_13_49_2
    | exact certificate_sound 13 49 3 cell_13_49_3
    | exact certificate_sound 13 49 4 cell_13_49_4
    | exact certificate_sound 13 49 5 cell_13_49_5
theorem cell_13_50_0 : CertificateAt 13 50 0 := by decide +kernel
theorem cell_13_50_1 : CertificateAt 13 50 1 := by decide +kernel
theorem cell_13_50_2 : CertificateAt 13 50 2 := by decide +kernel
theorem cell_13_50_3 : CertificateAt 13 50 3 := by decide +kernel
theorem cell_13_50_4 : CertificateAt 13 50 4 := by decide +kernel
theorem cell_13_50_5 : CertificateAt 13 50 5 := by decide +kernel
theorem row_13_50 : ThresholdAt 13 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 50 0 cell_13_50_0
    | exact certificate_sound 13 50 1 cell_13_50_1
    | exact certificate_sound 13 50 2 cell_13_50_2
    | exact certificate_sound 13 50 3 cell_13_50_3
    | exact certificate_sound 13 50 4 cell_13_50_4
    | exact certificate_sound 13 50 5 cell_13_50_5
theorem cell_13_51_0 : CertificateAt 13 51 0 := by decide +kernel
theorem cell_13_51_1 : CertificateAt 13 51 1 := by decide +kernel
theorem cell_13_51_2 : CertificateAt 13 51 2 := by decide +kernel
theorem cell_13_51_3 : CertificateAt 13 51 3 := by decide +kernel
theorem cell_13_51_4 : CertificateAt 13 51 4 := by decide +kernel
theorem cell_13_51_5 : CertificateAt 13 51 5 := by decide +kernel
theorem row_13_51 : ThresholdAt 13 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 51 0 cell_13_51_0
    | exact certificate_sound 13 51 1 cell_13_51_1
    | exact certificate_sound 13 51 2 cell_13_51_2
    | exact certificate_sound 13 51 3 cell_13_51_3
    | exact certificate_sound 13 51 4 cell_13_51_4
    | exact certificate_sound 13 51 5 cell_13_51_5
theorem cell_13_52_0 : CertificateAt 13 52 0 := by decide +kernel
theorem cell_13_52_1 : CertificateAt 13 52 1 := by decide +kernel
theorem cell_13_52_2 : CertificateAt 13 52 2 := by decide +kernel
theorem cell_13_52_3 : CertificateAt 13 52 3 := by decide +kernel
theorem cell_13_52_4 : CertificateAt 13 52 4 := by decide +kernel
theorem cell_13_52_5 : CertificateAt 13 52 5 := by decide +kernel
theorem row_13_52 : ThresholdAt 13 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 52 0 cell_13_52_0
    | exact certificate_sound 13 52 1 cell_13_52_1
    | exact certificate_sound 13 52 2 cell_13_52_2
    | exact certificate_sound 13 52 3 cell_13_52_3
    | exact certificate_sound 13 52 4 cell_13_52_4
    | exact certificate_sound 13 52 5 cell_13_52_5
theorem cell_13_53_0 : CertificateAt 13 53 0 := by decide +kernel
theorem cell_13_53_1 : CertificateAt 13 53 1 := by decide +kernel
theorem cell_13_53_2 : CertificateAt 13 53 2 := by decide +kernel
theorem cell_13_53_3 : CertificateAt 13 53 3 := by decide +kernel
theorem cell_13_53_4 : CertificateAt 13 53 4 := by decide +kernel
theorem cell_13_53_5 : CertificateAt 13 53 5 := by decide +kernel
theorem row_13_53 : ThresholdAt 13 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 53 0 cell_13_53_0
    | exact certificate_sound 13 53 1 cell_13_53_1
    | exact certificate_sound 13 53 2 cell_13_53_2
    | exact certificate_sound 13 53 3 cell_13_53_3
    | exact certificate_sound 13 53 4 cell_13_53_4
    | exact certificate_sound 13 53 5 cell_13_53_5
theorem cell_13_54_0 : CertificateAt 13 54 0 := by decide +kernel
theorem cell_13_54_1 : CertificateAt 13 54 1 := by decide +kernel
theorem cell_13_54_2 : CertificateAt 13 54 2 := by decide +kernel
theorem cell_13_54_3 : CertificateAt 13 54 3 := by decide +kernel
theorem cell_13_54_4 : CertificateAt 13 54 4 := by decide +kernel
theorem cell_13_54_5 : CertificateAt 13 54 5 := by decide +kernel
theorem row_13_54 : ThresholdAt 13 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 54 0 cell_13_54_0
    | exact certificate_sound 13 54 1 cell_13_54_1
    | exact certificate_sound 13 54 2 cell_13_54_2
    | exact certificate_sound 13 54 3 cell_13_54_3
    | exact certificate_sound 13 54 4 cell_13_54_4
    | exact certificate_sound 13 54 5 cell_13_54_5
theorem cell_13_55_0 : CertificateAt 13 55 0 := by decide +kernel
theorem cell_13_55_1 : CertificateAt 13 55 1 := by decide +kernel
theorem cell_13_55_2 : CertificateAt 13 55 2 := by decide +kernel
theorem cell_13_55_3 : CertificateAt 13 55 3 := by decide +kernel
theorem cell_13_55_4 : CertificateAt 13 55 4 := by decide +kernel
theorem cell_13_55_5 : CertificateAt 13 55 5 := by decide +kernel
theorem row_13_55 : ThresholdAt 13 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 55 0 cell_13_55_0
    | exact certificate_sound 13 55 1 cell_13_55_1
    | exact certificate_sound 13 55 2 cell_13_55_2
    | exact certificate_sound 13 55 3 cell_13_55_3
    | exact certificate_sound 13 55 4 cell_13_55_4
    | exact certificate_sound 13 55 5 cell_13_55_5
theorem cell_13_56_0 : CertificateAt 13 56 0 := by decide +kernel
theorem cell_13_56_1 : CertificateAt 13 56 1 := by decide +kernel
theorem cell_13_56_2 : CertificateAt 13 56 2 := by decide +kernel
theorem cell_13_56_3 : CertificateAt 13 56 3 := by decide +kernel
theorem cell_13_56_4 : CertificateAt 13 56 4 := by decide +kernel
theorem cell_13_56_5 : CertificateAt 13 56 5 := by decide +kernel
theorem row_13_56 : ThresholdAt 13 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 56 0 cell_13_56_0
    | exact certificate_sound 13 56 1 cell_13_56_1
    | exact certificate_sound 13 56 2 cell_13_56_2
    | exact certificate_sound 13 56 3 cell_13_56_3
    | exact certificate_sound 13 56 4 cell_13_56_4
    | exact certificate_sound 13 56 5 cell_13_56_5
theorem cell_13_57_0 : CertificateAt 13 57 0 := by decide +kernel
theorem cell_13_57_1 : CertificateAt 13 57 1 := by decide +kernel
theorem cell_13_57_2 : CertificateAt 13 57 2 := by decide +kernel
theorem cell_13_57_3 : CertificateAt 13 57 3 := by decide +kernel
theorem cell_13_57_4 : CertificateAt 13 57 4 := by decide +kernel
theorem cell_13_57_5 : CertificateAt 13 57 5 := by decide +kernel
theorem row_13_57 : ThresholdAt 13 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 57 0 cell_13_57_0
    | exact certificate_sound 13 57 1 cell_13_57_1
    | exact certificate_sound 13 57 2 cell_13_57_2
    | exact certificate_sound 13 57 3 cell_13_57_3
    | exact certificate_sound 13 57 4 cell_13_57_4
    | exact certificate_sound 13 57 5 cell_13_57_5
theorem cell_13_58_0 : CertificateAt 13 58 0 := by decide +kernel
theorem cell_13_58_1 : CertificateAt 13 58 1 := by decide +kernel
theorem cell_13_58_2 : CertificateAt 13 58 2 := by decide +kernel
theorem cell_13_58_3 : CertificateAt 13 58 3 := by decide +kernel
theorem cell_13_58_4 : CertificateAt 13 58 4 := by decide +kernel
theorem cell_13_58_5 : CertificateAt 13 58 5 := by decide +kernel
theorem row_13_58 : ThresholdAt 13 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 58 0 cell_13_58_0
    | exact certificate_sound 13 58 1 cell_13_58_1
    | exact certificate_sound 13 58 2 cell_13_58_2
    | exact certificate_sound 13 58 3 cell_13_58_3
    | exact certificate_sound 13 58 4 cell_13_58_4
    | exact certificate_sound 13 58 5 cell_13_58_5
theorem cell_13_59_0 : CertificateAt 13 59 0 := by decide +kernel
theorem cell_13_59_1 : CertificateAt 13 59 1 := by decide +kernel
theorem cell_13_59_2 : CertificateAt 13 59 2 := by decide +kernel
theorem cell_13_59_3 : CertificateAt 13 59 3 := by decide +kernel
theorem cell_13_59_4 : CertificateAt 13 59 4 := by decide +kernel
theorem cell_13_59_5 : CertificateAt 13 59 5 := by decide +kernel
theorem row_13_59 : ThresholdAt 13 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 59 0 cell_13_59_0
    | exact certificate_sound 13 59 1 cell_13_59_1
    | exact certificate_sound 13 59 2 cell_13_59_2
    | exact certificate_sound 13 59 3 cell_13_59_3
    | exact certificate_sound 13 59 4 cell_13_59_4
    | exact certificate_sound 13 59 5 cell_13_59_5
theorem cell_13_60_0 : CertificateAt 13 60 0 := by decide +kernel
theorem cell_13_60_1 : CertificateAt 13 60 1 := by decide +kernel
theorem cell_13_60_2 : CertificateAt 13 60 2 := by decide +kernel
theorem cell_13_60_3 : CertificateAt 13 60 3 := by decide +kernel
theorem cell_13_60_4 : CertificateAt 13 60 4 := by decide +kernel
theorem cell_13_60_5 : CertificateAt 13 60 5 := by decide +kernel
theorem row_13_60 : ThresholdAt 13 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 60 0 cell_13_60_0
    | exact certificate_sound 13 60 1 cell_13_60_1
    | exact certificate_sound 13 60 2 cell_13_60_2
    | exact certificate_sound 13 60 3 cell_13_60_3
    | exact certificate_sound 13 60 4 cell_13_60_4
    | exact certificate_sound 13 60 5 cell_13_60_5
theorem cell_13_61_0 : CertificateAt 13 61 0 := by decide +kernel
theorem cell_13_61_1 : CertificateAt 13 61 1 := by decide +kernel
theorem cell_13_61_2 : CertificateAt 13 61 2 := by decide +kernel
theorem cell_13_61_3 : CertificateAt 13 61 3 := by decide +kernel
theorem cell_13_61_4 : CertificateAt 13 61 4 := by decide +kernel
theorem cell_13_61_5 : CertificateAt 13 61 5 := by decide +kernel
theorem row_13_61 : ThresholdAt 13 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 61 0 cell_13_61_0
    | exact certificate_sound 13 61 1 cell_13_61_1
    | exact certificate_sound 13 61 2 cell_13_61_2
    | exact certificate_sound 13 61 3 cell_13_61_3
    | exact certificate_sound 13 61 4 cell_13_61_4
    | exact certificate_sound 13 61 5 cell_13_61_5
theorem cell_13_62_0 : CertificateAt 13 62 0 := by decide +kernel
theorem cell_13_62_1 : CertificateAt 13 62 1 := by decide +kernel
theorem cell_13_62_2 : CertificateAt 13 62 2 := by decide +kernel
theorem cell_13_62_3 : CertificateAt 13 62 3 := by decide +kernel
theorem cell_13_62_4 : CertificateAt 13 62 4 := by decide +kernel
theorem cell_13_62_5 : CertificateAt 13 62 5 := by decide +kernel
theorem row_13_62 : ThresholdAt 13 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 62 0 cell_13_62_0
    | exact certificate_sound 13 62 1 cell_13_62_1
    | exact certificate_sound 13 62 2 cell_13_62_2
    | exact certificate_sound 13 62 3 cell_13_62_3
    | exact certificate_sound 13 62 4 cell_13_62_4
    | exact certificate_sound 13 62 5 cell_13_62_5
theorem cell_13_63_0 : CertificateAt 13 63 0 := by decide +kernel
theorem cell_13_63_1 : CertificateAt 13 63 1 := by decide +kernel
theorem cell_13_63_2 : CertificateAt 13 63 2 := by decide +kernel
theorem cell_13_63_3 : CertificateAt 13 63 3 := by decide +kernel
theorem cell_13_63_4 : CertificateAt 13 63 4 := by decide +kernel
theorem cell_13_63_5 : CertificateAt 13 63 5 := by decide +kernel
theorem row_13_63 : ThresholdAt 13 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 63 0 cell_13_63_0
    | exact certificate_sound 13 63 1 cell_13_63_1
    | exact certificate_sound 13 63 2 cell_13_63_2
    | exact certificate_sound 13 63 3 cell_13_63_3
    | exact certificate_sound 13 63 4 cell_13_63_4
    | exact certificate_sound 13 63 5 cell_13_63_5
theorem cell_13_64_0 : CertificateAt 13 64 0 := by decide +kernel
theorem cell_13_64_1 : CertificateAt 13 64 1 := by decide +kernel
theorem cell_13_64_2 : CertificateAt 13 64 2 := by decide +kernel
theorem cell_13_64_3 : CertificateAt 13 64 3 := by decide +kernel
theorem cell_13_64_4 : CertificateAt 13 64 4 := by decide +kernel
theorem cell_13_64_5 : CertificateAt 13 64 5 := by decide +kernel
theorem row_13_64 : ThresholdAt 13 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 64 0 cell_13_64_0
    | exact certificate_sound 13 64 1 cell_13_64_1
    | exact certificate_sound 13 64 2 cell_13_64_2
    | exact certificate_sound 13 64 3 cell_13_64_3
    | exact certificate_sound 13 64 4 cell_13_64_4
    | exact certificate_sound 13 64 5 cell_13_64_5
theorem cell_13_65_0 : CertificateAt 13 65 0 := by decide +kernel
theorem cell_13_65_1 : CertificateAt 13 65 1 := by decide +kernel
theorem cell_13_65_2 : CertificateAt 13 65 2 := by decide +kernel
theorem cell_13_65_3 : CertificateAt 13 65 3 := by decide +kernel
theorem cell_13_65_4 : CertificateAt 13 65 4 := by decide +kernel
theorem cell_13_65_5 : CertificateAt 13 65 5 := by decide +kernel
theorem row_13_65 : ThresholdAt 13 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 65 0 cell_13_65_0
    | exact certificate_sound 13 65 1 cell_13_65_1
    | exact certificate_sound 13 65 2 cell_13_65_2
    | exact certificate_sound 13 65 3 cell_13_65_3
    | exact certificate_sound 13 65 4 cell_13_65_4
    | exact certificate_sound 13 65 5 cell_13_65_5
theorem cell_13_66_0 : CertificateAt 13 66 0 := by decide +kernel
theorem cell_13_66_1 : CertificateAt 13 66 1 := by decide +kernel
theorem cell_13_66_2 : CertificateAt 13 66 2 := by decide +kernel
theorem cell_13_66_3 : CertificateAt 13 66 3 := by decide +kernel
theorem cell_13_66_4 : CertificateAt 13 66 4 := by decide +kernel
theorem cell_13_66_5 : CertificateAt 13 66 5 := by decide +kernel
theorem row_13_66 : ThresholdAt 13 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 66 0 cell_13_66_0
    | exact certificate_sound 13 66 1 cell_13_66_1
    | exact certificate_sound 13 66 2 cell_13_66_2
    | exact certificate_sound 13 66 3 cell_13_66_3
    | exact certificate_sound 13 66 4 cell_13_66_4
    | exact certificate_sound 13 66 5 cell_13_66_5
theorem cell_13_67_0 : CertificateAt 13 67 0 := by decide +kernel
theorem cell_13_67_1 : CertificateAt 13 67 1 := by decide +kernel
theorem cell_13_67_2 : CertificateAt 13 67 2 := by decide +kernel
theorem cell_13_67_3 : CertificateAt 13 67 3 := by decide +kernel
theorem cell_13_67_4 : CertificateAt 13 67 4 := by decide +kernel
theorem cell_13_67_5 : CertificateAt 13 67 5 := by decide +kernel
theorem row_13_67 : ThresholdAt 13 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 67 0 cell_13_67_0
    | exact certificate_sound 13 67 1 cell_13_67_1
    | exact certificate_sound 13 67 2 cell_13_67_2
    | exact certificate_sound 13 67 3 cell_13_67_3
    | exact certificate_sound 13 67 4 cell_13_67_4
    | exact certificate_sound 13 67 5 cell_13_67_5
theorem cell_13_68_0 : CertificateAt 13 68 0 := by decide +kernel
theorem cell_13_68_1 : CertificateAt 13 68 1 := by decide +kernel
theorem cell_13_68_2 : CertificateAt 13 68 2 := by decide +kernel
theorem cell_13_68_3 : CertificateAt 13 68 3 := by decide +kernel
theorem cell_13_68_4 : CertificateAt 13 68 4 := by decide +kernel
theorem cell_13_68_5 : CertificateAt 13 68 5 := by decide +kernel
theorem row_13_68 : ThresholdAt 13 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 68 0 cell_13_68_0
    | exact certificate_sound 13 68 1 cell_13_68_1
    | exact certificate_sound 13 68 2 cell_13_68_2
    | exact certificate_sound 13 68 3 cell_13_68_3
    | exact certificate_sound 13 68 4 cell_13_68_4
    | exact certificate_sound 13 68 5 cell_13_68_5
theorem cell_13_69_0 : CertificateAt 13 69 0 := by decide +kernel
theorem cell_13_69_1 : CertificateAt 13 69 1 := by decide +kernel
theorem cell_13_69_2 : CertificateAt 13 69 2 := by decide +kernel
theorem cell_13_69_3 : CertificateAt 13 69 3 := by decide +kernel
theorem cell_13_69_4 : CertificateAt 13 69 4 := by decide +kernel
theorem cell_13_69_5 : CertificateAt 13 69 5 := by decide +kernel
theorem row_13_69 : ThresholdAt 13 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 69 0 cell_13_69_0
    | exact certificate_sound 13 69 1 cell_13_69_1
    | exact certificate_sound 13 69 2 cell_13_69_2
    | exact certificate_sound 13 69 3 cell_13_69_3
    | exact certificate_sound 13 69 4 cell_13_69_4
    | exact certificate_sound 13 69 5 cell_13_69_5
theorem cell_13_70_0 : CertificateAt 13 70 0 := by decide +kernel
theorem cell_13_70_1 : CertificateAt 13 70 1 := by decide +kernel
theorem cell_13_70_2 : CertificateAt 13 70 2 := by decide +kernel
theorem cell_13_70_3 : CertificateAt 13 70 3 := by decide +kernel
theorem cell_13_70_4 : CertificateAt 13 70 4 := by decide +kernel
theorem cell_13_70_5 : CertificateAt 13 70 5 := by decide +kernel
theorem row_13_70 : ThresholdAt 13 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 70 0 cell_13_70_0
    | exact certificate_sound 13 70 1 cell_13_70_1
    | exact certificate_sound 13 70 2 cell_13_70_2
    | exact certificate_sound 13 70 3 cell_13_70_3
    | exact certificate_sound 13 70 4 cell_13_70_4
    | exact certificate_sound 13 70 5 cell_13_70_5
theorem cell_13_71_0 : CertificateAt 13 71 0 := by decide +kernel
theorem cell_13_71_1 : CertificateAt 13 71 1 := by decide +kernel
theorem cell_13_71_2 : CertificateAt 13 71 2 := by decide +kernel
theorem cell_13_71_3 : CertificateAt 13 71 3 := by decide +kernel
theorem cell_13_71_4 : CertificateAt 13 71 4 := by decide +kernel
theorem cell_13_71_5 : CertificateAt 13 71 5 := by decide +kernel
theorem row_13_71 : ThresholdAt 13 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 71 0 cell_13_71_0
    | exact certificate_sound 13 71 1 cell_13_71_1
    | exact certificate_sound 13 71 2 cell_13_71_2
    | exact certificate_sound 13 71 3 cell_13_71_3
    | exact certificate_sound 13 71 4 cell_13_71_4
    | exact certificate_sound 13 71 5 cell_13_71_5
theorem cell_13_72_0 : CertificateAt 13 72 0 := by decide +kernel
theorem cell_13_72_1 : CertificateAt 13 72 1 := by decide +kernel
theorem cell_13_72_2 : CertificateAt 13 72 2 := by decide +kernel
theorem cell_13_72_3 : CertificateAt 13 72 3 := by decide +kernel
theorem cell_13_72_4 : CertificateAt 13 72 4 := by decide +kernel
theorem cell_13_72_5 : CertificateAt 13 72 5 := by decide +kernel
theorem row_13_72 : ThresholdAt 13 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 72 0 cell_13_72_0
    | exact certificate_sound 13 72 1 cell_13_72_1
    | exact certificate_sound 13 72 2 cell_13_72_2
    | exact certificate_sound 13 72 3 cell_13_72_3
    | exact certificate_sound 13 72 4 cell_13_72_4
    | exact certificate_sound 13 72 5 cell_13_72_5
theorem cell_13_73_0 : CertificateAt 13 73 0 := by decide +kernel
theorem cell_13_73_1 : CertificateAt 13 73 1 := by decide +kernel
theorem cell_13_73_2 : CertificateAt 13 73 2 := by decide +kernel
theorem cell_13_73_3 : CertificateAt 13 73 3 := by decide +kernel
theorem cell_13_73_4 : CertificateAt 13 73 4 := by decide +kernel
theorem cell_13_73_5 : CertificateAt 13 73 5 := by decide +kernel
theorem row_13_73 : ThresholdAt 13 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 73 0 cell_13_73_0
    | exact certificate_sound 13 73 1 cell_13_73_1
    | exact certificate_sound 13 73 2 cell_13_73_2
    | exact certificate_sound 13 73 3 cell_13_73_3
    | exact certificate_sound 13 73 4 cell_13_73_4
    | exact certificate_sound 13 73 5 cell_13_73_5
theorem cell_13_74_0 : CertificateAt 13 74 0 := by decide +kernel
theorem cell_13_74_1 : CertificateAt 13 74 1 := by decide +kernel
theorem cell_13_74_2 : CertificateAt 13 74 2 := by decide +kernel
theorem cell_13_74_3 : CertificateAt 13 74 3 := by decide +kernel
theorem cell_13_74_4 : CertificateAt 13 74 4 := by decide +kernel
theorem cell_13_74_5 : CertificateAt 13 74 5 := by decide +kernel
theorem row_13_74 : ThresholdAt 13 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 74 0 cell_13_74_0
    | exact certificate_sound 13 74 1 cell_13_74_1
    | exact certificate_sound 13 74 2 cell_13_74_2
    | exact certificate_sound 13 74 3 cell_13_74_3
    | exact certificate_sound 13 74 4 cell_13_74_4
    | exact certificate_sound 13 74 5 cell_13_74_5
theorem cell_13_75_0 : CertificateAt 13 75 0 := by decide +kernel
theorem cell_13_75_1 : CertificateAt 13 75 1 := by decide +kernel
theorem cell_13_75_2 : CertificateAt 13 75 2 := by decide +kernel
theorem cell_13_75_3 : CertificateAt 13 75 3 := by decide +kernel
theorem cell_13_75_4 : CertificateAt 13 75 4 := by decide +kernel
theorem cell_13_75_5 : CertificateAt 13 75 5 := by decide +kernel
theorem row_13_75 : ThresholdAt 13 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 75 0 cell_13_75_0
    | exact certificate_sound 13 75 1 cell_13_75_1
    | exact certificate_sound 13 75 2 cell_13_75_2
    | exact certificate_sound 13 75 3 cell_13_75_3
    | exact certificate_sound 13 75 4 cell_13_75_4
    | exact certificate_sound 13 75 5 cell_13_75_5
theorem cell_13_76_0 : CertificateAt 13 76 0 := by decide +kernel
theorem cell_13_76_1 : CertificateAt 13 76 1 := by decide +kernel
theorem cell_13_76_2 : CertificateAt 13 76 2 := by decide +kernel
theorem cell_13_76_3 : CertificateAt 13 76 3 := by decide +kernel
theorem cell_13_76_4 : CertificateAt 13 76 4 := by decide +kernel
theorem cell_13_76_5 : CertificateAt 13 76 5 := by decide +kernel
theorem row_13_76 : ThresholdAt 13 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 76 0 cell_13_76_0
    | exact certificate_sound 13 76 1 cell_13_76_1
    | exact certificate_sound 13 76 2 cell_13_76_2
    | exact certificate_sound 13 76 3 cell_13_76_3
    | exact certificate_sound 13 76 4 cell_13_76_4
    | exact certificate_sound 13 76 5 cell_13_76_5
theorem cell_13_77_0 : CertificateAt 13 77 0 := by decide +kernel
theorem cell_13_77_1 : CertificateAt 13 77 1 := by decide +kernel
theorem cell_13_77_2 : CertificateAt 13 77 2 := by decide +kernel
theorem cell_13_77_3 : CertificateAt 13 77 3 := by decide +kernel
theorem cell_13_77_4 : CertificateAt 13 77 4 := by decide +kernel
theorem cell_13_77_5 : CertificateAt 13 77 5 := by decide +kernel
theorem row_13_77 : ThresholdAt 13 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 77 0 cell_13_77_0
    | exact certificate_sound 13 77 1 cell_13_77_1
    | exact certificate_sound 13 77 2 cell_13_77_2
    | exact certificate_sound 13 77 3 cell_13_77_3
    | exact certificate_sound 13 77 4 cell_13_77_4
    | exact certificate_sound 13 77 5 cell_13_77_5
theorem cell_13_78_0 : CertificateAt 13 78 0 := by decide +kernel
theorem cell_13_78_1 : CertificateAt 13 78 1 := by decide +kernel
theorem cell_13_78_2 : CertificateAt 13 78 2 := by decide +kernel
theorem cell_13_78_3 : CertificateAt 13 78 3 := by decide +kernel
theorem cell_13_78_4 : CertificateAt 13 78 4 := by decide +kernel
theorem cell_13_78_5 : CertificateAt 13 78 5 := by decide +kernel
theorem row_13_78 : ThresholdAt 13 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 78 0 cell_13_78_0
    | exact certificate_sound 13 78 1 cell_13_78_1
    | exact certificate_sound 13 78 2 cell_13_78_2
    | exact certificate_sound 13 78 3 cell_13_78_3
    | exact certificate_sound 13 78 4 cell_13_78_4
    | exact certificate_sound 13 78 5 cell_13_78_5
theorem cell_13_79_0 : CertificateAt 13 79 0 := by decide +kernel
theorem cell_13_79_1 : CertificateAt 13 79 1 := by decide +kernel
theorem cell_13_79_2 : CertificateAt 13 79 2 := by decide +kernel
theorem cell_13_79_3 : CertificateAt 13 79 3 := by decide +kernel
theorem cell_13_79_4 : CertificateAt 13 79 4 := by decide +kernel
theorem cell_13_79_5 : CertificateAt 13 79 5 := by decide +kernel
theorem row_13_79 : ThresholdAt 13 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 79 0 cell_13_79_0
    | exact certificate_sound 13 79 1 cell_13_79_1
    | exact certificate_sound 13 79 2 cell_13_79_2
    | exact certificate_sound 13 79 3 cell_13_79_3
    | exact certificate_sound 13 79 4 cell_13_79_4
    | exact certificate_sound 13 79 5 cell_13_79_5
theorem cell_13_80_0 : CertificateAt 13 80 0 := by decide +kernel
theorem cell_13_80_1 : CertificateAt 13 80 1 := by decide +kernel
theorem cell_13_80_2 : CertificateAt 13 80 2 := by decide +kernel
theorem cell_13_80_3 : CertificateAt 13 80 3 := by decide +kernel
theorem cell_13_80_4 : CertificateAt 13 80 4 := by decide +kernel
theorem cell_13_80_5 : CertificateAt 13 80 5 := by decide +kernel
theorem row_13_80 : ThresholdAt 13 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 80 0 cell_13_80_0
    | exact certificate_sound 13 80 1 cell_13_80_1
    | exact certificate_sound 13 80 2 cell_13_80_2
    | exact certificate_sound 13 80 3 cell_13_80_3
    | exact certificate_sound 13 80 4 cell_13_80_4
    | exact certificate_sound 13 80 5 cell_13_80_5
theorem cell_13_81_0 : CertificateAt 13 81 0 := by decide +kernel
theorem cell_13_81_1 : CertificateAt 13 81 1 := by decide +kernel
theorem cell_13_81_2 : CertificateAt 13 81 2 := by decide +kernel
theorem cell_13_81_3 : CertificateAt 13 81 3 := by decide +kernel
theorem cell_13_81_4 : CertificateAt 13 81 4 := by decide +kernel
theorem cell_13_81_5 : CertificateAt 13 81 5 := by decide +kernel
theorem row_13_81 : ThresholdAt 13 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 81 0 cell_13_81_0
    | exact certificate_sound 13 81 1 cell_13_81_1
    | exact certificate_sound 13 81 2 cell_13_81_2
    | exact certificate_sound 13 81 3 cell_13_81_3
    | exact certificate_sound 13 81 4 cell_13_81_4
    | exact certificate_sound 13 81 5 cell_13_81_5
theorem cell_13_82_0 : CertificateAt 13 82 0 := by decide +kernel
theorem cell_13_82_1 : CertificateAt 13 82 1 := by decide +kernel
theorem cell_13_82_2 : CertificateAt 13 82 2 := by decide +kernel
theorem cell_13_82_3 : CertificateAt 13 82 3 := by decide +kernel
theorem cell_13_82_4 : CertificateAt 13 82 4 := by decide +kernel
theorem cell_13_82_5 : CertificateAt 13 82 5 := by decide +kernel
theorem row_13_82 : ThresholdAt 13 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 82 0 cell_13_82_0
    | exact certificate_sound 13 82 1 cell_13_82_1
    | exact certificate_sound 13 82 2 cell_13_82_2
    | exact certificate_sound 13 82 3 cell_13_82_3
    | exact certificate_sound 13 82 4 cell_13_82_4
    | exact certificate_sound 13 82 5 cell_13_82_5
theorem cell_13_83_0 : CertificateAt 13 83 0 := by decide +kernel
theorem cell_13_83_1 : CertificateAt 13 83 1 := by decide +kernel
theorem cell_13_83_2 : CertificateAt 13 83 2 := by decide +kernel
theorem cell_13_83_3 : CertificateAt 13 83 3 := by decide +kernel
theorem cell_13_83_4 : CertificateAt 13 83 4 := by decide +kernel
theorem cell_13_83_5 : CertificateAt 13 83 5 := by decide +kernel
theorem row_13_83 : ThresholdAt 13 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 83 0 cell_13_83_0
    | exact certificate_sound 13 83 1 cell_13_83_1
    | exact certificate_sound 13 83 2 cell_13_83_2
    | exact certificate_sound 13 83 3 cell_13_83_3
    | exact certificate_sound 13 83 4 cell_13_83_4
    | exact certificate_sound 13 83 5 cell_13_83_5
theorem cell_13_84_0 : CertificateAt 13 84 0 := by decide +kernel
theorem cell_13_84_1 : CertificateAt 13 84 1 := by decide +kernel
theorem cell_13_84_2 : CertificateAt 13 84 2 := by decide +kernel
theorem cell_13_84_3 : CertificateAt 13 84 3 := by decide +kernel
theorem cell_13_84_4 : CertificateAt 13 84 4 := by decide +kernel
theorem cell_13_84_5 : CertificateAt 13 84 5 := by decide +kernel
theorem row_13_84 : ThresholdAt 13 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 84 0 cell_13_84_0
    | exact certificate_sound 13 84 1 cell_13_84_1
    | exact certificate_sound 13 84 2 cell_13_84_2
    | exact certificate_sound 13 84 3 cell_13_84_3
    | exact certificate_sound 13 84 4 cell_13_84_4
    | exact certificate_sound 13 84 5 cell_13_84_5
theorem cell_13_85_0 : CertificateAt 13 85 0 := by decide +kernel
theorem cell_13_85_1 : CertificateAt 13 85 1 := by decide +kernel
theorem cell_13_85_2 : CertificateAt 13 85 2 := by decide +kernel
theorem cell_13_85_3 : CertificateAt 13 85 3 := by decide +kernel
theorem cell_13_85_4 : CertificateAt 13 85 4 := by decide +kernel
theorem cell_13_85_5 : CertificateAt 13 85 5 := by decide +kernel
theorem row_13_85 : ThresholdAt 13 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 85 0 cell_13_85_0
    | exact certificate_sound 13 85 1 cell_13_85_1
    | exact certificate_sound 13 85 2 cell_13_85_2
    | exact certificate_sound 13 85 3 cell_13_85_3
    | exact certificate_sound 13 85 4 cell_13_85_4
    | exact certificate_sound 13 85 5 cell_13_85_5
theorem cell_13_86_0 : CertificateAt 13 86 0 := by decide +kernel
theorem cell_13_86_1 : CertificateAt 13 86 1 := by decide +kernel
theorem cell_13_86_2 : CertificateAt 13 86 2 := by decide +kernel
theorem cell_13_86_3 : CertificateAt 13 86 3 := by decide +kernel
theorem cell_13_86_4 : CertificateAt 13 86 4 := by decide +kernel
theorem cell_13_86_5 : CertificateAt 13 86 5 := by decide +kernel
theorem row_13_86 : ThresholdAt 13 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 86 0 cell_13_86_0
    | exact certificate_sound 13 86 1 cell_13_86_1
    | exact certificate_sound 13 86 2 cell_13_86_2
    | exact certificate_sound 13 86 3 cell_13_86_3
    | exact certificate_sound 13 86 4 cell_13_86_4
    | exact certificate_sound 13 86 5 cell_13_86_5
theorem cell_13_87_0 : CertificateAt 13 87 0 := by decide +kernel
theorem cell_13_87_1 : CertificateAt 13 87 1 := by decide +kernel
theorem cell_13_87_2 : CertificateAt 13 87 2 := by decide +kernel
theorem cell_13_87_3 : CertificateAt 13 87 3 := by decide +kernel
theorem cell_13_87_4 : CertificateAt 13 87 4 := by decide +kernel
theorem cell_13_87_5 : CertificateAt 13 87 5 := by decide +kernel
theorem row_13_87 : ThresholdAt 13 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 87 0 cell_13_87_0
    | exact certificate_sound 13 87 1 cell_13_87_1
    | exact certificate_sound 13 87 2 cell_13_87_2
    | exact certificate_sound 13 87 3 cell_13_87_3
    | exact certificate_sound 13 87 4 cell_13_87_4
    | exact certificate_sound 13 87 5 cell_13_87_5
theorem cell_13_88_0 : CertificateAt 13 88 0 := by decide +kernel
theorem cell_13_88_1 : CertificateAt 13 88 1 := by decide +kernel
theorem cell_13_88_2 : CertificateAt 13 88 2 := by decide +kernel
theorem cell_13_88_3 : CertificateAt 13 88 3 := by decide +kernel
theorem cell_13_88_4 : CertificateAt 13 88 4 := by decide +kernel
theorem cell_13_88_5 : CertificateAt 13 88 5 := by decide +kernel
theorem row_13_88 : ThresholdAt 13 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 88 0 cell_13_88_0
    | exact certificate_sound 13 88 1 cell_13_88_1
    | exact certificate_sound 13 88 2 cell_13_88_2
    | exact certificate_sound 13 88 3 cell_13_88_3
    | exact certificate_sound 13 88 4 cell_13_88_4
    | exact certificate_sound 13 88 5 cell_13_88_5
theorem cell_13_89_0 : CertificateAt 13 89 0 := by decide +kernel
theorem cell_13_89_1 : CertificateAt 13 89 1 := by decide +kernel
theorem cell_13_89_2 : CertificateAt 13 89 2 := by decide +kernel
theorem cell_13_89_3 : CertificateAt 13 89 3 := by decide +kernel
theorem cell_13_89_4 : CertificateAt 13 89 4 := by decide +kernel
theorem cell_13_89_5 : CertificateAt 13 89 5 := by decide +kernel
theorem row_13_89 : ThresholdAt 13 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 89 0 cell_13_89_0
    | exact certificate_sound 13 89 1 cell_13_89_1
    | exact certificate_sound 13 89 2 cell_13_89_2
    | exact certificate_sound 13 89 3 cell_13_89_3
    | exact certificate_sound 13 89 4 cell_13_89_4
    | exact certificate_sound 13 89 5 cell_13_89_5
theorem cell_13_90_0 : CertificateAt 13 90 0 := by decide +kernel
theorem cell_13_90_1 : CertificateAt 13 90 1 := by decide +kernel
theorem cell_13_90_2 : CertificateAt 13 90 2 := by decide +kernel
theorem cell_13_90_3 : CertificateAt 13 90 3 := by decide +kernel
theorem cell_13_90_4 : CertificateAt 13 90 4 := by decide +kernel
theorem cell_13_90_5 : CertificateAt 13 90 5 := by decide +kernel
theorem row_13_90 : ThresholdAt 13 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 90 0 cell_13_90_0
    | exact certificate_sound 13 90 1 cell_13_90_1
    | exact certificate_sound 13 90 2 cell_13_90_2
    | exact certificate_sound 13 90 3 cell_13_90_3
    | exact certificate_sound 13 90 4 cell_13_90_4
    | exact certificate_sound 13 90 5 cell_13_90_5
theorem cell_13_91_0 : CertificateAt 13 91 0 := by decide +kernel
theorem cell_13_91_1 : CertificateAt 13 91 1 := by decide +kernel
theorem cell_13_91_2 : CertificateAt 13 91 2 := by decide +kernel
theorem cell_13_91_3 : CertificateAt 13 91 3 := by decide +kernel
theorem cell_13_91_4 : CertificateAt 13 91 4 := by decide +kernel
theorem cell_13_91_5 : CertificateAt 13 91 5 := by decide +kernel
theorem row_13_91 : ThresholdAt 13 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 91 0 cell_13_91_0
    | exact certificate_sound 13 91 1 cell_13_91_1
    | exact certificate_sound 13 91 2 cell_13_91_2
    | exact certificate_sound 13 91 3 cell_13_91_3
    | exact certificate_sound 13 91 4 cell_13_91_4
    | exact certificate_sound 13 91 5 cell_13_91_5
theorem cell_13_92_0 : CertificateAt 13 92 0 := by decide +kernel
theorem cell_13_92_1 : CertificateAt 13 92 1 := by decide +kernel
theorem cell_13_92_2 : CertificateAt 13 92 2 := by decide +kernel
theorem cell_13_92_3 : CertificateAt 13 92 3 := by decide +kernel
theorem cell_13_92_4 : CertificateAt 13 92 4 := by decide +kernel
theorem cell_13_92_5 : CertificateAt 13 92 5 := by decide +kernel
theorem row_13_92 : ThresholdAt 13 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 92 0 cell_13_92_0
    | exact certificate_sound 13 92 1 cell_13_92_1
    | exact certificate_sound 13 92 2 cell_13_92_2
    | exact certificate_sound 13 92 3 cell_13_92_3
    | exact certificate_sound 13 92 4 cell_13_92_4
    | exact certificate_sound 13 92 5 cell_13_92_5
theorem cell_13_93_0 : CertificateAt 13 93 0 := by decide +kernel
theorem cell_13_93_1 : CertificateAt 13 93 1 := by decide +kernel
theorem cell_13_93_2 : CertificateAt 13 93 2 := by decide +kernel
theorem cell_13_93_3 : CertificateAt 13 93 3 := by decide +kernel
theorem cell_13_93_4 : CertificateAt 13 93 4 := by decide +kernel
theorem cell_13_93_5 : CertificateAt 13 93 5 := by decide +kernel
theorem row_13_93 : ThresholdAt 13 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 93 0 cell_13_93_0
    | exact certificate_sound 13 93 1 cell_13_93_1
    | exact certificate_sound 13 93 2 cell_13_93_2
    | exact certificate_sound 13 93 3 cell_13_93_3
    | exact certificate_sound 13 93 4 cell_13_93_4
    | exact certificate_sound 13 93 5 cell_13_93_5
theorem cell_13_94_0 : CertificateAt 13 94 0 := by decide +kernel
theorem cell_13_94_1 : CertificateAt 13 94 1 := by decide +kernel
theorem cell_13_94_2 : CertificateAt 13 94 2 := by decide +kernel
theorem cell_13_94_3 : CertificateAt 13 94 3 := by decide +kernel
theorem cell_13_94_4 : CertificateAt 13 94 4 := by decide +kernel
theorem cell_13_94_5 : CertificateAt 13 94 5 := by decide +kernel
theorem row_13_94 : ThresholdAt 13 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 94 0 cell_13_94_0
    | exact certificate_sound 13 94 1 cell_13_94_1
    | exact certificate_sound 13 94 2 cell_13_94_2
    | exact certificate_sound 13 94 3 cell_13_94_3
    | exact certificate_sound 13 94 4 cell_13_94_4
    | exact certificate_sound 13 94 5 cell_13_94_5
theorem cell_13_95_0 : CertificateAt 13 95 0 := by decide +kernel
theorem cell_13_95_1 : CertificateAt 13 95 1 := by decide +kernel
theorem cell_13_95_2 : CertificateAt 13 95 2 := by decide +kernel
theorem cell_13_95_3 : CertificateAt 13 95 3 := by decide +kernel
theorem cell_13_95_4 : CertificateAt 13 95 4 := by decide +kernel
theorem cell_13_95_5 : CertificateAt 13 95 5 := by decide +kernel
theorem row_13_95 : ThresholdAt 13 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 95 0 cell_13_95_0
    | exact certificate_sound 13 95 1 cell_13_95_1
    | exact certificate_sound 13 95 2 cell_13_95_2
    | exact certificate_sound 13 95 3 cell_13_95_3
    | exact certificate_sound 13 95 4 cell_13_95_4
    | exact certificate_sound 13 95 5 cell_13_95_5
theorem cell_13_96_0 : CertificateAt 13 96 0 := by decide +kernel
theorem cell_13_96_1 : CertificateAt 13 96 1 := by decide +kernel
theorem cell_13_96_2 : CertificateAt 13 96 2 := by decide +kernel
theorem cell_13_96_3 : CertificateAt 13 96 3 := by decide +kernel
theorem cell_13_96_4 : CertificateAt 13 96 4 := by decide +kernel
theorem cell_13_96_5 : CertificateAt 13 96 5 := by decide +kernel
theorem row_13_96 : ThresholdAt 13 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 96 0 cell_13_96_0
    | exact certificate_sound 13 96 1 cell_13_96_1
    | exact certificate_sound 13 96 2 cell_13_96_2
    | exact certificate_sound 13 96 3 cell_13_96_3
    | exact certificate_sound 13 96 4 cell_13_96_4
    | exact certificate_sound 13 96 5 cell_13_96_5
theorem cell_13_97_0 : CertificateAt 13 97 0 := by decide +kernel
theorem cell_13_97_1 : CertificateAt 13 97 1 := by decide +kernel
theorem cell_13_97_2 : CertificateAt 13 97 2 := by decide +kernel
theorem cell_13_97_3 : CertificateAt 13 97 3 := by decide +kernel
theorem cell_13_97_4 : CertificateAt 13 97 4 := by decide +kernel
theorem cell_13_97_5 : CertificateAt 13 97 5 := by decide +kernel
theorem row_13_97 : ThresholdAt 13 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 97 0 cell_13_97_0
    | exact certificate_sound 13 97 1 cell_13_97_1
    | exact certificate_sound 13 97 2 cell_13_97_2
    | exact certificate_sound 13 97 3 cell_13_97_3
    | exact certificate_sound 13 97 4 cell_13_97_4
    | exact certificate_sound 13 97 5 cell_13_97_5
theorem cell_13_98_0 : CertificateAt 13 98 0 := by decide +kernel
theorem cell_13_98_1 : CertificateAt 13 98 1 := by decide +kernel
theorem cell_13_98_2 : CertificateAt 13 98 2 := by decide +kernel
theorem cell_13_98_3 : CertificateAt 13 98 3 := by decide +kernel
theorem cell_13_98_4 : CertificateAt 13 98 4 := by decide +kernel
theorem cell_13_98_5 : CertificateAt 13 98 5 := by decide +kernel
theorem row_13_98 : ThresholdAt 13 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 98 0 cell_13_98_0
    | exact certificate_sound 13 98 1 cell_13_98_1
    | exact certificate_sound 13 98 2 cell_13_98_2
    | exact certificate_sound 13 98 3 cell_13_98_3
    | exact certificate_sound 13 98 4 cell_13_98_4
    | exact certificate_sound 13 98 5 cell_13_98_5
theorem cell_13_99_0 : CertificateAt 13 99 0 := by decide +kernel
theorem cell_13_99_1 : CertificateAt 13 99 1 := by decide +kernel
theorem cell_13_99_2 : CertificateAt 13 99 2 := by decide +kernel
theorem cell_13_99_3 : CertificateAt 13 99 3 := by decide +kernel
theorem cell_13_99_4 : CertificateAt 13 99 4 := by decide +kernel
theorem cell_13_99_5 : CertificateAt 13 99 5 := by decide +kernel
theorem row_13_99 : ThresholdAt 13 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 99 0 cell_13_99_0
    | exact certificate_sound 13 99 1 cell_13_99_1
    | exact certificate_sound 13 99 2 cell_13_99_2
    | exact certificate_sound 13 99 3 cell_13_99_3
    | exact certificate_sound 13 99 4 cell_13_99_4
    | exact certificate_sound 13 99 5 cell_13_99_5
theorem cell_13_100_0 : CertificateAt 13 100 0 := by decide +kernel
theorem cell_13_100_1 : CertificateAt 13 100 1 := by decide +kernel
theorem cell_13_100_2 : CertificateAt 13 100 2 := by decide +kernel
theorem cell_13_100_3 : CertificateAt 13 100 3 := by decide +kernel
theorem cell_13_100_4 : CertificateAt 13 100 4 := by decide +kernel
theorem cell_13_100_5 : CertificateAt 13 100 5 := by decide +kernel
theorem row_13_100 : ThresholdAt 13 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 100 0 cell_13_100_0
    | exact certificate_sound 13 100 1 cell_13_100_1
    | exact certificate_sound 13 100 2 cell_13_100_2
    | exact certificate_sound 13 100 3 cell_13_100_3
    | exact certificate_sound 13 100 4 cell_13_100_4
    | exact certificate_sound 13 100 5 cell_13_100_5
theorem cell_13_101_0 : CertificateAt 13 101 0 := by decide +kernel
theorem cell_13_101_1 : CertificateAt 13 101 1 := by decide +kernel
theorem cell_13_101_2 : CertificateAt 13 101 2 := by decide +kernel
theorem cell_13_101_3 : CertificateAt 13 101 3 := by decide +kernel
theorem cell_13_101_4 : CertificateAt 13 101 4 := by decide +kernel
theorem cell_13_101_5 : CertificateAt 13 101 5 := by decide +kernel
theorem row_13_101 : ThresholdAt 13 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 101 0 cell_13_101_0
    | exact certificate_sound 13 101 1 cell_13_101_1
    | exact certificate_sound 13 101 2 cell_13_101_2
    | exact certificate_sound 13 101 3 cell_13_101_3
    | exact certificate_sound 13 101 4 cell_13_101_4
    | exact certificate_sound 13 101 5 cell_13_101_5
theorem cell_13_102_0 : CertificateAt 13 102 0 := by decide +kernel
theorem cell_13_102_1 : CertificateAt 13 102 1 := by decide +kernel
theorem cell_13_102_2 : CertificateAt 13 102 2 := by decide +kernel
theorem cell_13_102_3 : CertificateAt 13 102 3 := by decide +kernel
theorem cell_13_102_4 : CertificateAt 13 102 4 := by decide +kernel
theorem cell_13_102_5 : CertificateAt 13 102 5 := by decide +kernel
theorem row_13_102 : ThresholdAt 13 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 102 0 cell_13_102_0
    | exact certificate_sound 13 102 1 cell_13_102_1
    | exact certificate_sound 13 102 2 cell_13_102_2
    | exact certificate_sound 13 102 3 cell_13_102_3
    | exact certificate_sound 13 102 4 cell_13_102_4
    | exact certificate_sound 13 102 5 cell_13_102_5
theorem cell_13_103_0 : CertificateAt 13 103 0 := by decide +kernel
theorem cell_13_103_1 : CertificateAt 13 103 1 := by decide +kernel
theorem cell_13_103_2 : CertificateAt 13 103 2 := by decide +kernel
theorem cell_13_103_3 : CertificateAt 13 103 3 := by decide +kernel
theorem cell_13_103_4 : CertificateAt 13 103 4 := by decide +kernel
theorem cell_13_103_5 : CertificateAt 13 103 5 := by decide +kernel
theorem row_13_103 : ThresholdAt 13 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 103 0 cell_13_103_0
    | exact certificate_sound 13 103 1 cell_13_103_1
    | exact certificate_sound 13 103 2 cell_13_103_2
    | exact certificate_sound 13 103 3 cell_13_103_3
    | exact certificate_sound 13 103 4 cell_13_103_4
    | exact certificate_sound 13 103 5 cell_13_103_5
theorem cell_13_104_0 : CertificateAt 13 104 0 := by decide +kernel
theorem cell_13_104_1 : CertificateAt 13 104 1 := by decide +kernel
theorem cell_13_104_2 : CertificateAt 13 104 2 := by decide +kernel
theorem cell_13_104_3 : CertificateAt 13 104 3 := by decide +kernel
theorem cell_13_104_4 : CertificateAt 13 104 4 := by decide +kernel
theorem cell_13_104_5 : CertificateAt 13 104 5 := by decide +kernel
theorem row_13_104 : ThresholdAt 13 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 104 0 cell_13_104_0
    | exact certificate_sound 13 104 1 cell_13_104_1
    | exact certificate_sound 13 104 2 cell_13_104_2
    | exact certificate_sound 13 104 3 cell_13_104_3
    | exact certificate_sound 13 104 4 cell_13_104_4
    | exact certificate_sound 13 104 5 cell_13_104_5
theorem cell_13_105_0 : CertificateAt 13 105 0 := by decide +kernel
theorem cell_13_105_1 : CertificateAt 13 105 1 := by decide +kernel
theorem cell_13_105_2 : CertificateAt 13 105 2 := by decide +kernel
theorem cell_13_105_3 : CertificateAt 13 105 3 := by decide +kernel
theorem cell_13_105_4 : CertificateAt 13 105 4 := by decide +kernel
theorem cell_13_105_5 : CertificateAt 13 105 5 := by decide +kernel
theorem row_13_105 : ThresholdAt 13 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 105 0 cell_13_105_0
    | exact certificate_sound 13 105 1 cell_13_105_1
    | exact certificate_sound 13 105 2 cell_13_105_2
    | exact certificate_sound 13 105 3 cell_13_105_3
    | exact certificate_sound 13 105 4 cell_13_105_4
    | exact certificate_sound 13 105 5 cell_13_105_5
theorem cell_13_106_0 : CertificateAt 13 106 0 := by decide +kernel
theorem cell_13_106_1 : CertificateAt 13 106 1 := by decide +kernel
theorem cell_13_106_2 : CertificateAt 13 106 2 := by decide +kernel
theorem cell_13_106_3 : CertificateAt 13 106 3 := by decide +kernel
theorem cell_13_106_4 : CertificateAt 13 106 4 := by decide +kernel
theorem cell_13_106_5 : CertificateAt 13 106 5 := by decide +kernel
theorem row_13_106 : ThresholdAt 13 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 106 0 cell_13_106_0
    | exact certificate_sound 13 106 1 cell_13_106_1
    | exact certificate_sound 13 106 2 cell_13_106_2
    | exact certificate_sound 13 106 3 cell_13_106_3
    | exact certificate_sound 13 106 4 cell_13_106_4
    | exact certificate_sound 13 106 5 cell_13_106_5
theorem cell_13_107_0 : CertificateAt 13 107 0 := by decide +kernel
theorem cell_13_107_1 : CertificateAt 13 107 1 := by decide +kernel
theorem cell_13_107_2 : CertificateAt 13 107 2 := by decide +kernel
theorem cell_13_107_3 : CertificateAt 13 107 3 := by decide +kernel
theorem cell_13_107_4 : CertificateAt 13 107 4 := by decide +kernel
theorem cell_13_107_5 : CertificateAt 13 107 5 := by decide +kernel
theorem row_13_107 : ThresholdAt 13 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 107 0 cell_13_107_0
    | exact certificate_sound 13 107 1 cell_13_107_1
    | exact certificate_sound 13 107 2 cell_13_107_2
    | exact certificate_sound 13 107 3 cell_13_107_3
    | exact certificate_sound 13 107 4 cell_13_107_4
    | exact certificate_sound 13 107 5 cell_13_107_5
theorem cell_13_108_0 : CertificateAt 13 108 0 := by decide +kernel
theorem cell_13_108_1 : CertificateAt 13 108 1 := by decide +kernel
theorem cell_13_108_2 : CertificateAt 13 108 2 := by decide +kernel
theorem cell_13_108_3 : CertificateAt 13 108 3 := by decide +kernel
theorem cell_13_108_4 : CertificateAt 13 108 4 := by decide +kernel
theorem cell_13_108_5 : CertificateAt 13 108 5 := by decide +kernel
theorem row_13_108 : ThresholdAt 13 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 108 0 cell_13_108_0
    | exact certificate_sound 13 108 1 cell_13_108_1
    | exact certificate_sound 13 108 2 cell_13_108_2
    | exact certificate_sound 13 108 3 cell_13_108_3
    | exact certificate_sound 13 108 4 cell_13_108_4
    | exact certificate_sound 13 108 5 cell_13_108_5
theorem cell_13_109_0 : CertificateAt 13 109 0 := by decide +kernel
theorem cell_13_109_1 : CertificateAt 13 109 1 := by decide +kernel
theorem cell_13_109_2 : CertificateAt 13 109 2 := by decide +kernel
theorem cell_13_109_3 : CertificateAt 13 109 3 := by decide +kernel
theorem cell_13_109_4 : CertificateAt 13 109 4 := by decide +kernel
theorem cell_13_109_5 : CertificateAt 13 109 5 := by decide +kernel
theorem row_13_109 : ThresholdAt 13 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 109 0 cell_13_109_0
    | exact certificate_sound 13 109 1 cell_13_109_1
    | exact certificate_sound 13 109 2 cell_13_109_2
    | exact certificate_sound 13 109 3 cell_13_109_3
    | exact certificate_sound 13 109 4 cell_13_109_4
    | exact certificate_sound 13 109 5 cell_13_109_5
theorem cell_13_110_0 : CertificateAt 13 110 0 := by decide +kernel
theorem cell_13_110_1 : CertificateAt 13 110 1 := by decide +kernel
theorem cell_13_110_2 : CertificateAt 13 110 2 := by decide +kernel
theorem cell_13_110_3 : CertificateAt 13 110 3 := by decide +kernel
theorem cell_13_110_4 : CertificateAt 13 110 4 := by decide +kernel
theorem cell_13_110_5 : CertificateAt 13 110 5 := by decide +kernel
theorem row_13_110 : ThresholdAt 13 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 110 0 cell_13_110_0
    | exact certificate_sound 13 110 1 cell_13_110_1
    | exact certificate_sound 13 110 2 cell_13_110_2
    | exact certificate_sound 13 110 3 cell_13_110_3
    | exact certificate_sound 13 110 4 cell_13_110_4
    | exact certificate_sound 13 110 5 cell_13_110_5
theorem cell_13_111_0 : CertificateAt 13 111 0 := by decide +kernel
theorem cell_13_111_1 : CertificateAt 13 111 1 := by decide +kernel
theorem cell_13_111_2 : CertificateAt 13 111 2 := by decide +kernel
theorem cell_13_111_3 : CertificateAt 13 111 3 := by decide +kernel
theorem cell_13_111_4 : CertificateAt 13 111 4 := by decide +kernel
theorem cell_13_111_5 : CertificateAt 13 111 5 := by decide +kernel
theorem row_13_111 : ThresholdAt 13 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 111 0 cell_13_111_0
    | exact certificate_sound 13 111 1 cell_13_111_1
    | exact certificate_sound 13 111 2 cell_13_111_2
    | exact certificate_sound 13 111 3 cell_13_111_3
    | exact certificate_sound 13 111 4 cell_13_111_4
    | exact certificate_sound 13 111 5 cell_13_111_5
theorem cell_13_112_0 : CertificateAt 13 112 0 := by decide +kernel
theorem cell_13_112_1 : CertificateAt 13 112 1 := by decide +kernel
theorem cell_13_112_2 : CertificateAt 13 112 2 := by decide +kernel
theorem cell_13_112_3 : CertificateAt 13 112 3 := by decide +kernel
theorem cell_13_112_4 : CertificateAt 13 112 4 := by decide +kernel
theorem cell_13_112_5 : CertificateAt 13 112 5 := by decide +kernel
theorem row_13_112 : ThresholdAt 13 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 112 0 cell_13_112_0
    | exact certificate_sound 13 112 1 cell_13_112_1
    | exact certificate_sound 13 112 2 cell_13_112_2
    | exact certificate_sound 13 112 3 cell_13_112_3
    | exact certificate_sound 13 112 4 cell_13_112_4
    | exact certificate_sound 13 112 5 cell_13_112_5
theorem cell_13_113_0 : CertificateAt 13 113 0 := by decide +kernel
theorem cell_13_113_1 : CertificateAt 13 113 1 := by decide +kernel
theorem cell_13_113_2 : CertificateAt 13 113 2 := by decide +kernel
theorem cell_13_113_3 : CertificateAt 13 113 3 := by decide +kernel
theorem cell_13_113_4 : CertificateAt 13 113 4 := by decide +kernel
theorem cell_13_113_5 : CertificateAt 13 113 5 := by decide +kernel
theorem row_13_113 : ThresholdAt 13 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 113 0 cell_13_113_0
    | exact certificate_sound 13 113 1 cell_13_113_1
    | exact certificate_sound 13 113 2 cell_13_113_2
    | exact certificate_sound 13 113 3 cell_13_113_3
    | exact certificate_sound 13 113 4 cell_13_113_4
    | exact certificate_sound 13 113 5 cell_13_113_5
theorem cell_13_114_0 : CertificateAt 13 114 0 := by decide +kernel
theorem cell_13_114_1 : CertificateAt 13 114 1 := by decide +kernel
theorem cell_13_114_2 : CertificateAt 13 114 2 := by decide +kernel
theorem cell_13_114_3 : CertificateAt 13 114 3 := by decide +kernel
theorem cell_13_114_4 : CertificateAt 13 114 4 := by decide +kernel
theorem cell_13_114_5 : CertificateAt 13 114 5 := by decide +kernel
theorem row_13_114 : ThresholdAt 13 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 114 0 cell_13_114_0
    | exact certificate_sound 13 114 1 cell_13_114_1
    | exact certificate_sound 13 114 2 cell_13_114_2
    | exact certificate_sound 13 114 3 cell_13_114_3
    | exact certificate_sound 13 114 4 cell_13_114_4
    | exact certificate_sound 13 114 5 cell_13_114_5
theorem cell_13_115_0 : CertificateAt 13 115 0 := by decide +kernel
theorem cell_13_115_1 : CertificateAt 13 115 1 := by decide +kernel
theorem cell_13_115_2 : CertificateAt 13 115 2 := by decide +kernel
theorem cell_13_115_3 : CertificateAt 13 115 3 := by decide +kernel
theorem cell_13_115_4 : CertificateAt 13 115 4 := by decide +kernel
theorem cell_13_115_5 : CertificateAt 13 115 5 := by decide +kernel
theorem row_13_115 : ThresholdAt 13 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 115 0 cell_13_115_0
    | exact certificate_sound 13 115 1 cell_13_115_1
    | exact certificate_sound 13 115 2 cell_13_115_2
    | exact certificate_sound 13 115 3 cell_13_115_3
    | exact certificate_sound 13 115 4 cell_13_115_4
    | exact certificate_sound 13 115 5 cell_13_115_5
theorem cell_13_116_0 : CertificateAt 13 116 0 := by decide +kernel
theorem cell_13_116_1 : CertificateAt 13 116 1 := by decide +kernel
theorem cell_13_116_2 : CertificateAt 13 116 2 := by decide +kernel
theorem cell_13_116_3 : CertificateAt 13 116 3 := by decide +kernel
theorem cell_13_116_4 : CertificateAt 13 116 4 := by decide +kernel
theorem cell_13_116_5 : CertificateAt 13 116 5 := by decide +kernel
theorem row_13_116 : ThresholdAt 13 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 116 0 cell_13_116_0
    | exact certificate_sound 13 116 1 cell_13_116_1
    | exact certificate_sound 13 116 2 cell_13_116_2
    | exact certificate_sound 13 116 3 cell_13_116_3
    | exact certificate_sound 13 116 4 cell_13_116_4
    | exact certificate_sound 13 116 5 cell_13_116_5
theorem cell_13_117_0 : CertificateAt 13 117 0 := by decide +kernel
theorem cell_13_117_1 : CertificateAt 13 117 1 := by decide +kernel
theorem cell_13_117_2 : CertificateAt 13 117 2 := by decide +kernel
theorem cell_13_117_3 : CertificateAt 13 117 3 := by decide +kernel
theorem cell_13_117_4 : CertificateAt 13 117 4 := by decide +kernel
theorem cell_13_117_5 : CertificateAt 13 117 5 := by decide +kernel
theorem row_13_117 : ThresholdAt 13 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 117 0 cell_13_117_0
    | exact certificate_sound 13 117 1 cell_13_117_1
    | exact certificate_sound 13 117 2 cell_13_117_2
    | exact certificate_sound 13 117 3 cell_13_117_3
    | exact certificate_sound 13 117 4 cell_13_117_4
    | exact certificate_sound 13 117 5 cell_13_117_5
theorem cell_13_118_0 : CertificateAt 13 118 0 := by decide +kernel
theorem cell_13_118_1 : CertificateAt 13 118 1 := by decide +kernel
theorem cell_13_118_2 : CertificateAt 13 118 2 := by decide +kernel
theorem cell_13_118_3 : CertificateAt 13 118 3 := by decide +kernel
theorem cell_13_118_4 : CertificateAt 13 118 4 := by decide +kernel
theorem cell_13_118_5 : CertificateAt 13 118 5 := by decide +kernel
theorem row_13_118 : ThresholdAt 13 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 118 0 cell_13_118_0
    | exact certificate_sound 13 118 1 cell_13_118_1
    | exact certificate_sound 13 118 2 cell_13_118_2
    | exact certificate_sound 13 118 3 cell_13_118_3
    | exact certificate_sound 13 118 4 cell_13_118_4
    | exact certificate_sound 13 118 5 cell_13_118_5
theorem cell_13_119_0 : CertificateAt 13 119 0 := by decide +kernel
theorem cell_13_119_1 : CertificateAt 13 119 1 := by decide +kernel
theorem cell_13_119_2 : CertificateAt 13 119 2 := by decide +kernel
theorem cell_13_119_3 : CertificateAt 13 119 3 := by decide +kernel
theorem cell_13_119_4 : CertificateAt 13 119 4 := by decide +kernel
theorem cell_13_119_5 : CertificateAt 13 119 5 := by decide +kernel
theorem row_13_119 : ThresholdAt 13 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 119 0 cell_13_119_0
    | exact certificate_sound 13 119 1 cell_13_119_1
    | exact certificate_sound 13 119 2 cell_13_119_2
    | exact certificate_sound 13 119 3 cell_13_119_3
    | exact certificate_sound 13 119 4 cell_13_119_4
    | exact certificate_sound 13 119 5 cell_13_119_5
theorem cell_13_120_0 : CertificateAt 13 120 0 := by decide +kernel
theorem cell_13_120_1 : CertificateAt 13 120 1 := by decide +kernel
theorem cell_13_120_2 : CertificateAt 13 120 2 := by decide +kernel
theorem cell_13_120_3 : CertificateAt 13 120 3 := by decide +kernel
theorem cell_13_120_4 : CertificateAt 13 120 4 := by decide +kernel
theorem cell_13_120_5 : CertificateAt 13 120 5 := by decide +kernel
theorem row_13_120 : ThresholdAt 13 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 120 0 cell_13_120_0
    | exact certificate_sound 13 120 1 cell_13_120_1
    | exact certificate_sound 13 120 2 cell_13_120_2
    | exact certificate_sound 13 120 3 cell_13_120_3
    | exact certificate_sound 13 120 4 cell_13_120_4
    | exact certificate_sound 13 120 5 cell_13_120_5
theorem cell_13_121_0 : CertificateAt 13 121 0 := by decide +kernel
theorem cell_13_121_1 : CertificateAt 13 121 1 := by decide +kernel
theorem cell_13_121_2 : CertificateAt 13 121 2 := by decide +kernel
theorem cell_13_121_3 : CertificateAt 13 121 3 := by decide +kernel
theorem cell_13_121_4 : CertificateAt 13 121 4 := by decide +kernel
theorem cell_13_121_5 : CertificateAt 13 121 5 := by decide +kernel
theorem row_13_121 : ThresholdAt 13 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 121 0 cell_13_121_0
    | exact certificate_sound 13 121 1 cell_13_121_1
    | exact certificate_sound 13 121 2 cell_13_121_2
    | exact certificate_sound 13 121 3 cell_13_121_3
    | exact certificate_sound 13 121 4 cell_13_121_4
    | exact certificate_sound 13 121 5 cell_13_121_5
theorem cell_13_122_0 : CertificateAt 13 122 0 := by decide +kernel
theorem cell_13_122_1 : CertificateAt 13 122 1 := by decide +kernel
theorem cell_13_122_2 : CertificateAt 13 122 2 := by decide +kernel
theorem cell_13_122_3 : CertificateAt 13 122 3 := by decide +kernel
theorem cell_13_122_4 : CertificateAt 13 122 4 := by decide +kernel
theorem cell_13_122_5 : CertificateAt 13 122 5 := by decide +kernel
theorem row_13_122 : ThresholdAt 13 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 122 0 cell_13_122_0
    | exact certificate_sound 13 122 1 cell_13_122_1
    | exact certificate_sound 13 122 2 cell_13_122_2
    | exact certificate_sound 13 122 3 cell_13_122_3
    | exact certificate_sound 13 122 4 cell_13_122_4
    | exact certificate_sound 13 122 5 cell_13_122_5
theorem cell_13_123_0 : CertificateAt 13 123 0 := by decide +kernel
theorem cell_13_123_1 : CertificateAt 13 123 1 := by decide +kernel
theorem cell_13_123_2 : CertificateAt 13 123 2 := by decide +kernel
theorem cell_13_123_3 : CertificateAt 13 123 3 := by decide +kernel
theorem cell_13_123_4 : CertificateAt 13 123 4 := by decide +kernel
theorem cell_13_123_5 : CertificateAt 13 123 5 := by decide +kernel
theorem row_13_123 : ThresholdAt 13 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 123 0 cell_13_123_0
    | exact certificate_sound 13 123 1 cell_13_123_1
    | exact certificate_sound 13 123 2 cell_13_123_2
    | exact certificate_sound 13 123 3 cell_13_123_3
    | exact certificate_sound 13 123 4 cell_13_123_4
    | exact certificate_sound 13 123 5 cell_13_123_5
theorem cell_13_124_0 : CertificateAt 13 124 0 := by decide +kernel
theorem cell_13_124_1 : CertificateAt 13 124 1 := by decide +kernel
theorem cell_13_124_2 : CertificateAt 13 124 2 := by decide +kernel
theorem cell_13_124_3 : CertificateAt 13 124 3 := by decide +kernel
theorem cell_13_124_4 : CertificateAt 13 124 4 := by decide +kernel
theorem cell_13_124_5 : CertificateAt 13 124 5 := by decide +kernel
theorem row_13_124 : ThresholdAt 13 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 124 0 cell_13_124_0
    | exact certificate_sound 13 124 1 cell_13_124_1
    | exact certificate_sound 13 124 2 cell_13_124_2
    | exact certificate_sound 13 124 3 cell_13_124_3
    | exact certificate_sound 13 124 4 cell_13_124_4
    | exact certificate_sound 13 124 5 cell_13_124_5
theorem cell_13_125_0 : CertificateAt 13 125 0 := by decide +kernel
theorem cell_13_125_1 : CertificateAt 13 125 1 := by decide +kernel
theorem cell_13_125_2 : CertificateAt 13 125 2 := by decide +kernel
theorem cell_13_125_3 : CertificateAt 13 125 3 := by decide +kernel
theorem cell_13_125_4 : CertificateAt 13 125 4 := by decide +kernel
theorem cell_13_125_5 : CertificateAt 13 125 5 := by decide +kernel
theorem row_13_125 : ThresholdAt 13 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 125 0 cell_13_125_0
    | exact certificate_sound 13 125 1 cell_13_125_1
    | exact certificate_sound 13 125 2 cell_13_125_2
    | exact certificate_sound 13 125 3 cell_13_125_3
    | exact certificate_sound 13 125 4 cell_13_125_4
    | exact certificate_sound 13 125 5 cell_13_125_5
theorem cell_13_126_0 : CertificateAt 13 126 0 := by decide +kernel
theorem cell_13_126_1 : CertificateAt 13 126 1 := by decide +kernel
theorem cell_13_126_2 : CertificateAt 13 126 2 := by decide +kernel
theorem cell_13_126_3 : CertificateAt 13 126 3 := by decide +kernel
theorem cell_13_126_4 : CertificateAt 13 126 4 := by decide +kernel
theorem cell_13_126_5 : CertificateAt 13 126 5 := by decide +kernel
theorem row_13_126 : ThresholdAt 13 126 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 13 126 0 cell_13_126_0
    | exact certificate_sound 13 126 1 cell_13_126_1
    | exact certificate_sound 13 126 2 cell_13_126_2
    | exact certificate_sound 13 126 3 cell_13_126_3
    | exact certificate_sound 13 126 4 cell_13_126_4
    | exact certificate_sound 13 126 5 cell_13_126_5
theorem checkedR13 : ∀ V ∈ List.range 127, ThresholdAt 13 V := by
  intro V hV
  have hv : V < 127 := List.mem_range.mp hV
  by_cases h0_127 : V < 63
  · by_cases h0_63 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_13_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_13_1
              · have he : V = 2 := by omega
                subst V
                exact row_13_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_13_3
              · have he : V = 4 := by omega
                subst V
                exact row_13_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_13_5
              · have he : V = 6 := by omega
                subst V
                exact row_13_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_13_7
              · have he : V = 8 := by omega
                subst V
                exact row_13_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_13_9
              · have he : V = 10 := by omega
                subst V
                exact row_13_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_13_11
              · have he : V = 12 := by omega
                subst V
                exact row_13_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_13_13
              · have he : V = 14 := by omega
                subst V
                exact row_13_14
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_13_15
              · have he : V = 16 := by omega
                subst V
                exact row_13_16
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_13_17
              · have he : V = 18 := by omega
                subst V
                exact row_13_18
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_13_19
              · have he : V = 20 := by omega
                subst V
                exact row_13_20
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_13_21
              · have he : V = 22 := by omega
                subst V
                exact row_13_22
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_13_23
              · have he : V = 24 := by omega
                subst V
                exact row_13_24
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_13_25
              · have he : V = 26 := by omega
                subst V
                exact row_13_26
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_13_27
              · have he : V = 28 := by omega
                subst V
                exact row_13_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_13_29
              · have he : V = 30 := by omega
                subst V
                exact row_13_30
    · by_cases h31_63 : V < 47
      · by_cases h31_47 : V < 39
        · by_cases h31_39 : V < 35
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_13_31
              · have he : V = 32 := by omega
                subst V
                exact row_13_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_13_33
              · have he : V = 34 := by omega
                subst V
                exact row_13_34
          · by_cases h35_39 : V < 37
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_13_35
              · have he : V = 36 := by omega
                subst V
                exact row_13_36
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_13_37
              · have he : V = 38 := by omega
                subst V
                exact row_13_38
        · by_cases h39_47 : V < 43
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_13_39
              · have he : V = 40 := by omega
                subst V
                exact row_13_40
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_13_41
              · have he : V = 42 := by omega
                subst V
                exact row_13_42
          · by_cases h43_47 : V < 45
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_13_43
              · have he : V = 44 := by omega
                subst V
                exact row_13_44
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_13_45
              · have he : V = 46 := by omega
                subst V
                exact row_13_46
      · by_cases h47_63 : V < 55
        · by_cases h47_55 : V < 51
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_13_47
              · have he : V = 48 := by omega
                subst V
                exact row_13_48
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_13_49
              · have he : V = 50 := by omega
                subst V
                exact row_13_50
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_13_51
              · have he : V = 52 := by omega
                subst V
                exact row_13_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_13_53
              · have he : V = 54 := by omega
                subst V
                exact row_13_54
        · by_cases h55_63 : V < 59
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_13_55
              · have he : V = 56 := by omega
                subst V
                exact row_13_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_13_57
              · have he : V = 58 := by omega
                subst V
                exact row_13_58
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_13_59
              · have he : V = 60 := by omega
                subst V
                exact row_13_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_13_61
              · have he : V = 62 := by omega
                subst V
                exact row_13_62
  · by_cases h63_127 : V < 95
    · by_cases h63_95 : V < 79
      · by_cases h63_79 : V < 71
        · by_cases h63_71 : V < 67
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_13_63
              · have he : V = 64 := by omega
                subst V
                exact row_13_64
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_13_65
              · have he : V = 66 := by omega
                subst V
                exact row_13_66
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_13_67
              · have he : V = 68 := by omega
                subst V
                exact row_13_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_13_69
              · have he : V = 70 := by omega
                subst V
                exact row_13_70
        · by_cases h71_79 : V < 75
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_13_71
              · have he : V = 72 := by omega
                subst V
                exact row_13_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_13_73
              · have he : V = 74 := by omega
                subst V
                exact row_13_74
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_13_75
              · have he : V = 76 := by omega
                subst V
                exact row_13_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_13_77
              · have he : V = 78 := by omega
                subst V
                exact row_13_78
      · by_cases h79_95 : V < 87
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_13_79
              · have he : V = 80 := by omega
                subst V
                exact row_13_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_13_81
              · have he : V = 82 := by omega
                subst V
                exact row_13_82
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_13_83
              · have he : V = 84 := by omega
                subst V
                exact row_13_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_13_85
              · have he : V = 86 := by omega
                subst V
                exact row_13_86
        · by_cases h87_95 : V < 91
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_13_87
              · have he : V = 88 := by omega
                subst V
                exact row_13_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_13_89
              · have he : V = 90 := by omega
                subst V
                exact row_13_90
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_13_91
              · have he : V = 92 := by omega
                subst V
                exact row_13_92
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_13_93
              · have he : V = 94 := by omega
                subst V
                exact row_13_94
    · by_cases h95_127 : V < 111
      · by_cases h95_111 : V < 103
        · by_cases h95_103 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_13_95
              · have he : V = 96 := by omega
                subst V
                exact row_13_96
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_13_97
              · have he : V = 98 := by omega
                subst V
                exact row_13_98
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_13_99
              · have he : V = 100 := by omega
                subst V
                exact row_13_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_13_101
              · have he : V = 102 := by omega
                subst V
                exact row_13_102
        · by_cases h103_111 : V < 107
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_13_103
              · have he : V = 104 := by omega
                subst V
                exact row_13_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_13_105
              · have he : V = 106 := by omega
                subst V
                exact row_13_106
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_13_107
              · have he : V = 108 := by omega
                subst V
                exact row_13_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_13_109
              · have he : V = 110 := by omega
                subst V
                exact row_13_110
      · by_cases h111_127 : V < 119
        · by_cases h111_119 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_13_111
              · have he : V = 112 := by omega
                subst V
                exact row_13_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_13_113
              · have he : V = 114 := by omega
                subst V
                exact row_13_114
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_13_115
              · have he : V = 116 := by omega
                subst V
                exact row_13_116
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_13_117
              · have he : V = 118 := by omega
                subst V
                exact row_13_118
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_13_119
              · have he : V = 120 := by omega
                subst V
                exact row_13_120
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_13_121
              · have he : V = 122 := by omega
                subst V
                exact row_13_122
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_13_123
              · have he : V = 124 := by omega
                subst V
                exact row_13_124
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_13_125
              · have he : V = 126 := by omega
                subst V
                exact row_13_126
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
