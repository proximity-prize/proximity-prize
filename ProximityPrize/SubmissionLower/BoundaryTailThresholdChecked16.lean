import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked15

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q16_0:ThresholdAt 16 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 0 0 (by decide +kernel)
  | exact S 16 0 1 (by decide +kernel)
  | exact S 16 0 2 (by decide +kernel)
  | exact S 16 0 3 (by decide +kernel)
  | exact S 16 0 4 (by decide +kernel)
  | exact S 16 0 5 (by decide +kernel)
theorem q16_1:ThresholdAt 16 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 1 0 (by decide +kernel)
  | exact S 16 1 1 (by decide +kernel)
  | exact S 16 1 2 (by decide +kernel)
  | exact S 16 1 3 (by decide +kernel)
  | exact S 16 1 4 (by decide +kernel)
  | exact S 16 1 5 (by decide +kernel)
theorem q16_2:ThresholdAt 16 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 2 0 (by decide +kernel)
  | exact S 16 2 1 (by decide +kernel)
  | exact S 16 2 2 (by decide +kernel)
  | exact S 16 2 3 (by decide +kernel)
  | exact S 16 2 4 (by decide +kernel)
  | exact S 16 2 5 (by decide +kernel)
theorem q16_3:ThresholdAt 16 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 3 0 (by decide +kernel)
  | exact S 16 3 1 (by decide +kernel)
  | exact S 16 3 2 (by decide +kernel)
  | exact S 16 3 3 (by decide +kernel)
  | exact S 16 3 4 (by decide +kernel)
  | exact S 16 3 5 (by decide +kernel)
theorem q16_4:ThresholdAt 16 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 4 0 (by decide +kernel)
  | exact S 16 4 1 (by decide +kernel)
  | exact S 16 4 2 (by decide +kernel)
  | exact S 16 4 3 (by decide +kernel)
  | exact S 16 4 4 (by decide +kernel)
  | exact S 16 4 5 (by decide +kernel)
theorem q16_5:ThresholdAt 16 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 5 0 (by decide +kernel)
  | exact S 16 5 1 (by decide +kernel)
  | exact S 16 5 2 (by decide +kernel)
  | exact S 16 5 3 (by decide +kernel)
  | exact S 16 5 4 (by decide +kernel)
  | exact S 16 5 5 (by decide +kernel)
theorem q16_6:ThresholdAt 16 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 6 0 (by decide +kernel)
  | exact S 16 6 1 (by decide +kernel)
  | exact S 16 6 2 (by decide +kernel)
  | exact S 16 6 3 (by decide +kernel)
  | exact S 16 6 4 (by decide +kernel)
  | exact S 16 6 5 (by decide +kernel)
theorem q16_7:ThresholdAt 16 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 7 0 (by decide +kernel)
  | exact S 16 7 1 (by decide +kernel)
  | exact S 16 7 2 (by decide +kernel)
  | exact S 16 7 3 (by decide +kernel)
  | exact S 16 7 4 (by decide +kernel)
  | exact S 16 7 5 (by decide +kernel)
theorem q16_8:ThresholdAt 16 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 8 0 (by decide +kernel)
  | exact S 16 8 1 (by decide +kernel)
  | exact S 16 8 2 (by decide +kernel)
  | exact S 16 8 3 (by decide +kernel)
  | exact S 16 8 4 (by decide +kernel)
  | exact S 16 8 5 (by decide +kernel)
theorem q16_9:ThresholdAt 16 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 9 0 (by decide +kernel)
  | exact S 16 9 1 (by decide +kernel)
  | exact S 16 9 2 (by decide +kernel)
  | exact S 16 9 3 (by decide +kernel)
  | exact S 16 9 4 (by decide +kernel)
  | exact S 16 9 5 (by decide +kernel)
theorem q16_10:ThresholdAt 16 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 10 0 (by decide +kernel)
  | exact S 16 10 1 (by decide +kernel)
  | exact S 16 10 2 (by decide +kernel)
  | exact S 16 10 3 (by decide +kernel)
  | exact S 16 10 4 (by decide +kernel)
  | exact S 16 10 5 (by decide +kernel)
theorem q16_11:ThresholdAt 16 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 11 0 (by decide +kernel)
  | exact S 16 11 1 (by decide +kernel)
  | exact S 16 11 2 (by decide +kernel)
  | exact S 16 11 3 (by decide +kernel)
  | exact S 16 11 4 (by decide +kernel)
  | exact S 16 11 5 (by decide +kernel)
theorem q16_12:ThresholdAt 16 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 12 0 (by decide +kernel)
  | exact S 16 12 1 (by decide +kernel)
  | exact S 16 12 2 (by decide +kernel)
  | exact S 16 12 3 (by decide +kernel)
  | exact S 16 12 4 (by decide +kernel)
  | exact S 16 12 5 (by decide +kernel)
theorem q16_13:ThresholdAt 16 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 13 0 (by decide +kernel)
  | exact S 16 13 1 (by decide +kernel)
  | exact S 16 13 2 (by decide +kernel)
  | exact S 16 13 3 (by decide +kernel)
  | exact S 16 13 4 (by decide +kernel)
  | exact S 16 13 5 (by decide +kernel)
theorem q16_14:ThresholdAt 16 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 14 0 (by decide +kernel)
  | exact S 16 14 1 (by decide +kernel)
  | exact S 16 14 2 (by decide +kernel)
  | exact S 16 14 3 (by decide +kernel)
  | exact S 16 14 4 (by decide +kernel)
  | exact S 16 14 5 (by decide +kernel)
theorem q16_15:ThresholdAt 16 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 15 0 (by decide +kernel)
  | exact S 16 15 1 (by decide +kernel)
  | exact S 16 15 2 (by decide +kernel)
  | exact S 16 15 3 (by decide +kernel)
  | exact S 16 15 4 (by decide +kernel)
  | exact S 16 15 5 (by decide +kernel)
theorem q16_16:ThresholdAt 16 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 16 0 (by decide +kernel)
  | exact S 16 16 1 (by decide +kernel)
  | exact S 16 16 2 (by decide +kernel)
  | exact S 16 16 3 (by decide +kernel)
  | exact S 16 16 4 (by decide +kernel)
  | exact S 16 16 5 (by decide +kernel)
theorem q16_17:ThresholdAt 16 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 17 0 (by decide +kernel)
  | exact S 16 17 1 (by decide +kernel)
  | exact S 16 17 2 (by decide +kernel)
  | exact S 16 17 3 (by decide +kernel)
  | exact S 16 17 4 (by decide +kernel)
  | exact S 16 17 5 (by decide +kernel)
theorem q16_18:ThresholdAt 16 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 18 0 (by decide +kernel)
  | exact S 16 18 1 (by decide +kernel)
  | exact S 16 18 2 (by decide +kernel)
  | exact S 16 18 3 (by decide +kernel)
  | exact S 16 18 4 (by decide +kernel)
  | exact S 16 18 5 (by decide +kernel)
theorem q16_19:ThresholdAt 16 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 19 0 (by decide +kernel)
  | exact S 16 19 1 (by decide +kernel)
  | exact S 16 19 2 (by decide +kernel)
  | exact S 16 19 3 (by decide +kernel)
  | exact S 16 19 4 (by decide +kernel)
  | exact S 16 19 5 (by decide +kernel)
theorem q16_20:ThresholdAt 16 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 20 0 (by decide +kernel)
  | exact S 16 20 1 (by decide +kernel)
  | exact S 16 20 2 (by decide +kernel)
  | exact S 16 20 3 (by decide +kernel)
  | exact S 16 20 4 (by decide +kernel)
  | exact S 16 20 5 (by decide +kernel)
theorem q16_21:ThresholdAt 16 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 21 0 (by decide +kernel)
  | exact S 16 21 1 (by decide +kernel)
  | exact S 16 21 2 (by decide +kernel)
  | exact S 16 21 3 (by decide +kernel)
  | exact S 16 21 4 (by decide +kernel)
  | exact S 16 21 5 (by decide +kernel)
theorem q16_22:ThresholdAt 16 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 22 0 (by decide +kernel)
  | exact S 16 22 1 (by decide +kernel)
  | exact S 16 22 2 (by decide +kernel)
  | exact S 16 22 3 (by decide +kernel)
  | exact S 16 22 4 (by decide +kernel)
  | exact S 16 22 5 (by decide +kernel)
theorem q16_23:ThresholdAt 16 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 23 0 (by decide +kernel)
  | exact S 16 23 1 (by decide +kernel)
  | exact S 16 23 2 (by decide +kernel)
  | exact S 16 23 3 (by decide +kernel)
  | exact S 16 23 4 (by decide +kernel)
  | exact S 16 23 5 (by decide +kernel)
theorem q16_24:ThresholdAt 16 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 24 0 (by decide +kernel)
  | exact S 16 24 1 (by decide +kernel)
  | exact S 16 24 2 (by decide +kernel)
  | exact S 16 24 3 (by decide +kernel)
  | exact S 16 24 4 (by decide +kernel)
  | exact S 16 24 5 (by decide +kernel)
theorem q16_25:ThresholdAt 16 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 25 0 (by decide +kernel)
  | exact S 16 25 1 (by decide +kernel)
  | exact S 16 25 2 (by decide +kernel)
  | exact S 16 25 3 (by decide +kernel)
  | exact S 16 25 4 (by decide +kernel)
  | exact S 16 25 5 (by decide +kernel)
theorem q16_26:ThresholdAt 16 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 26 0 (by decide +kernel)
  | exact S 16 26 1 (by decide +kernel)
  | exact S 16 26 2 (by decide +kernel)
  | exact S 16 26 3 (by decide +kernel)
  | exact S 16 26 4 (by decide +kernel)
  | exact S 16 26 5 (by decide +kernel)
theorem q16_27:ThresholdAt 16 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 27 0 (by decide +kernel)
  | exact S 16 27 1 (by decide +kernel)
  | exact S 16 27 2 (by decide +kernel)
  | exact S 16 27 3 (by decide +kernel)
  | exact S 16 27 4 (by decide +kernel)
  | exact S 16 27 5 (by decide +kernel)
theorem q16_28:ThresholdAt 16 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 28 0 (by decide +kernel)
  | exact S 16 28 1 (by decide +kernel)
  | exact S 16 28 2 (by decide +kernel)
  | exact S 16 28 3 (by decide +kernel)
  | exact S 16 28 4 (by decide +kernel)
  | exact S 16 28 5 (by decide +kernel)
theorem q16_29:ThresholdAt 16 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 29 0 (by decide +kernel)
  | exact S 16 29 1 (by decide +kernel)
  | exact S 16 29 2 (by decide +kernel)
  | exact S 16 29 3 (by decide +kernel)
  | exact S 16 29 4 (by decide +kernel)
  | exact S 16 29 5 (by decide +kernel)
theorem q16_30:ThresholdAt 16 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 30 0 (by decide +kernel)
  | exact S 16 30 1 (by decide +kernel)
  | exact S 16 30 2 (by decide +kernel)
  | exact S 16 30 3 (by decide +kernel)
  | exact S 16 30 4 (by decide +kernel)
  | exact S 16 30 5 (by decide +kernel)
theorem q16_31:ThresholdAt 16 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 31 0 (by decide +kernel)
  | exact S 16 31 1 (by decide +kernel)
  | exact S 16 31 2 (by decide +kernel)
  | exact S 16 31 3 (by decide +kernel)
  | exact S 16 31 4 (by decide +kernel)
  | exact S 16 31 5 (by decide +kernel)
theorem q16_32:ThresholdAt 16 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 32 0 (by decide +kernel)
  | exact S 16 32 1 (by decide +kernel)
  | exact S 16 32 2 (by decide +kernel)
  | exact S 16 32 3 (by decide +kernel)
  | exact S 16 32 4 (by decide +kernel)
  | exact S 16 32 5 (by decide +kernel)
theorem q16_33:ThresholdAt 16 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 33 0 (by decide +kernel)
  | exact S 16 33 1 (by decide +kernel)
  | exact S 16 33 2 (by decide +kernel)
  | exact S 16 33 3 (by decide +kernel)
  | exact S 16 33 4 (by decide +kernel)
  | exact S 16 33 5 (by decide +kernel)
theorem q16_34:ThresholdAt 16 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 34 0 (by decide +kernel)
  | exact S 16 34 1 (by decide +kernel)
  | exact S 16 34 2 (by decide +kernel)
  | exact S 16 34 3 (by decide +kernel)
  | exact S 16 34 4 (by decide +kernel)
  | exact S 16 34 5 (by decide +kernel)
theorem q16_35:ThresholdAt 16 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 35 0 (by decide +kernel)
  | exact S 16 35 1 (by decide +kernel)
  | exact S 16 35 2 (by decide +kernel)
  | exact S 16 35 3 (by decide +kernel)
  | exact S 16 35 4 (by decide +kernel)
  | exact S 16 35 5 (by decide +kernel)
theorem q16_36:ThresholdAt 16 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 36 0 (by decide +kernel)
  | exact S 16 36 1 (by decide +kernel)
  | exact S 16 36 2 (by decide +kernel)
  | exact S 16 36 3 (by decide +kernel)
  | exact S 16 36 4 (by decide +kernel)
  | exact S 16 36 5 (by decide +kernel)
theorem q16_37:ThresholdAt 16 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 37 0 (by decide +kernel)
  | exact S 16 37 1 (by decide +kernel)
  | exact S 16 37 2 (by decide +kernel)
  | exact S 16 37 3 (by decide +kernel)
  | exact S 16 37 4 (by decide +kernel)
  | exact S 16 37 5 (by decide +kernel)
theorem q16_38:ThresholdAt 16 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 38 0 (by decide +kernel)
  | exact S 16 38 1 (by decide +kernel)
  | exact S 16 38 2 (by decide +kernel)
  | exact S 16 38 3 (by decide +kernel)
  | exact S 16 38 4 (by decide +kernel)
  | exact S 16 38 5 (by decide +kernel)
theorem q16_39:ThresholdAt 16 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 39 0 (by decide +kernel)
  | exact S 16 39 1 (by decide +kernel)
  | exact S 16 39 2 (by decide +kernel)
  | exact S 16 39 3 (by decide +kernel)
  | exact S 16 39 4 (by decide +kernel)
  | exact S 16 39 5 (by decide +kernel)
theorem q16_40:ThresholdAt 16 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 40 0 (by decide +kernel)
  | exact S 16 40 1 (by decide +kernel)
  | exact S 16 40 2 (by decide +kernel)
  | exact S 16 40 3 (by decide +kernel)
  | exact S 16 40 4 (by decide +kernel)
  | exact S 16 40 5 (by decide +kernel)
theorem q16_41:ThresholdAt 16 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 41 0 (by decide +kernel)
  | exact S 16 41 1 (by decide +kernel)
  | exact S 16 41 2 (by decide +kernel)
  | exact S 16 41 3 (by decide +kernel)
  | exact S 16 41 4 (by decide +kernel)
  | exact S 16 41 5 (by decide +kernel)
theorem q16_42:ThresholdAt 16 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 42 0 (by decide +kernel)
  | exact S 16 42 1 (by decide +kernel)
  | exact S 16 42 2 (by decide +kernel)
  | exact S 16 42 3 (by decide +kernel)
  | exact S 16 42 4 (by decide +kernel)
  | exact S 16 42 5 (by decide +kernel)
theorem q16_43:ThresholdAt 16 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 43 0 (by decide +kernel)
  | exact S 16 43 1 (by decide +kernel)
  | exact S 16 43 2 (by decide +kernel)
  | exact S 16 43 3 (by decide +kernel)
  | exact S 16 43 4 (by decide +kernel)
  | exact S 16 43 5 (by decide +kernel)
theorem q16_44:ThresholdAt 16 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 44 0 (by decide +kernel)
  | exact S 16 44 1 (by decide +kernel)
  | exact S 16 44 2 (by decide +kernel)
  | exact S 16 44 3 (by decide +kernel)
  | exact S 16 44 4 (by decide +kernel)
  | exact S 16 44 5 (by decide +kernel)
theorem q16_45:ThresholdAt 16 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 45 0 (by decide +kernel)
  | exact S 16 45 1 (by decide +kernel)
  | exact S 16 45 2 (by decide +kernel)
  | exact S 16 45 3 (by decide +kernel)
  | exact S 16 45 4 (by decide +kernel)
  | exact S 16 45 5 (by decide +kernel)
theorem q16_46:ThresholdAt 16 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 46 0 (by decide +kernel)
  | exact S 16 46 1 (by decide +kernel)
  | exact S 16 46 2 (by decide +kernel)
  | exact S 16 46 3 (by decide +kernel)
  | exact S 16 46 4 (by decide +kernel)
  | exact S 16 46 5 (by decide +kernel)
theorem q16_47:ThresholdAt 16 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 47 0 (by decide +kernel)
  | exact S 16 47 1 (by decide +kernel)
  | exact S 16 47 2 (by decide +kernel)
  | exact S 16 47 3 (by decide +kernel)
  | exact S 16 47 4 (by decide +kernel)
  | exact S 16 47 5 (by decide +kernel)
theorem q16_48:ThresholdAt 16 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 48 0 (by decide +kernel)
  | exact S 16 48 1 (by decide +kernel)
  | exact S 16 48 2 (by decide +kernel)
  | exact S 16 48 3 (by decide +kernel)
  | exact S 16 48 4 (by decide +kernel)
  | exact S 16 48 5 (by decide +kernel)
theorem q16_49:ThresholdAt 16 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 49 0 (by decide +kernel)
  | exact S 16 49 1 (by decide +kernel)
  | exact S 16 49 2 (by decide +kernel)
  | exact S 16 49 3 (by decide +kernel)
  | exact S 16 49 4 (by decide +kernel)
  | exact S 16 49 5 (by decide +kernel)
theorem q16_50:ThresholdAt 16 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 50 0 (by decide +kernel)
  | exact S 16 50 1 (by decide +kernel)
  | exact S 16 50 2 (by decide +kernel)
  | exact S 16 50 3 (by decide +kernel)
  | exact S 16 50 4 (by decide +kernel)
  | exact S 16 50 5 (by decide +kernel)
theorem q16_51:ThresholdAt 16 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 51 0 (by decide +kernel)
  | exact S 16 51 1 (by decide +kernel)
  | exact S 16 51 2 (by decide +kernel)
  | exact S 16 51 3 (by decide +kernel)
  | exact S 16 51 4 (by decide +kernel)
  | exact S 16 51 5 (by decide +kernel)
theorem q16_52:ThresholdAt 16 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 52 0 (by decide +kernel)
  | exact S 16 52 1 (by decide +kernel)
  | exact S 16 52 2 (by decide +kernel)
  | exact S 16 52 3 (by decide +kernel)
  | exact S 16 52 4 (by decide +kernel)
  | exact S 16 52 5 (by decide +kernel)
theorem q16_53:ThresholdAt 16 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 53 0 (by decide +kernel)
  | exact S 16 53 1 (by decide +kernel)
  | exact S 16 53 2 (by decide +kernel)
  | exact S 16 53 3 (by decide +kernel)
  | exact S 16 53 4 (by decide +kernel)
  | exact S 16 53 5 (by decide +kernel)
theorem q16_54:ThresholdAt 16 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 54 0 (by decide +kernel)
  | exact S 16 54 1 (by decide +kernel)
  | exact S 16 54 2 (by decide +kernel)
  | exact S 16 54 3 (by decide +kernel)
  | exact S 16 54 4 (by decide +kernel)
  | exact S 16 54 5 (by decide +kernel)
theorem q16_55:ThresholdAt 16 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 55 0 (by decide +kernel)
  | exact S 16 55 1 (by decide +kernel)
  | exact S 16 55 2 (by decide +kernel)
  | exact S 16 55 3 (by decide +kernel)
  | exact S 16 55 4 (by decide +kernel)
  | exact S 16 55 5 (by decide +kernel)
theorem q16_56:ThresholdAt 16 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 56 0 (by decide +kernel)
  | exact S 16 56 1 (by decide +kernel)
  | exact S 16 56 2 (by decide +kernel)
  | exact S 16 56 3 (by decide +kernel)
  | exact S 16 56 4 (by decide +kernel)
  | exact S 16 56 5 (by decide +kernel)
theorem q16_57:ThresholdAt 16 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 57 0 (by decide +kernel)
  | exact S 16 57 1 (by decide +kernel)
  | exact S 16 57 2 (by decide +kernel)
  | exact S 16 57 3 (by decide +kernel)
  | exact S 16 57 4 (by decide +kernel)
  | exact S 16 57 5 (by decide +kernel)
theorem q16_58:ThresholdAt 16 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 58 0 (by decide +kernel)
  | exact S 16 58 1 (by decide +kernel)
  | exact S 16 58 2 (by decide +kernel)
  | exact S 16 58 3 (by decide +kernel)
  | exact S 16 58 4 (by decide +kernel)
  | exact S 16 58 5 (by decide +kernel)
theorem q16_59:ThresholdAt 16 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 59 0 (by decide +kernel)
  | exact S 16 59 1 (by decide +kernel)
  | exact S 16 59 2 (by decide +kernel)
  | exact S 16 59 3 (by decide +kernel)
  | exact S 16 59 4 (by decide +kernel)
  | exact S 16 59 5 (by decide +kernel)
theorem q16_60:ThresholdAt 16 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 60 0 (by decide +kernel)
  | exact S 16 60 1 (by decide +kernel)
  | exact S 16 60 2 (by decide +kernel)
  | exact S 16 60 3 (by decide +kernel)
  | exact S 16 60 4 (by decide +kernel)
  | exact S 16 60 5 (by decide +kernel)
theorem q16_61:ThresholdAt 16 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 61 0 (by decide +kernel)
  | exact S 16 61 1 (by decide +kernel)
  | exact S 16 61 2 (by decide +kernel)
  | exact S 16 61 3 (by decide +kernel)
  | exact S 16 61 4 (by decide +kernel)
  | exact S 16 61 5 (by decide +kernel)
theorem q16_62:ThresholdAt 16 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 62 0 (by decide +kernel)
  | exact S 16 62 1 (by decide +kernel)
  | exact S 16 62 2 (by decide +kernel)
  | exact S 16 62 3 (by decide +kernel)
  | exact S 16 62 4 (by decide +kernel)
  | exact S 16 62 5 (by decide +kernel)
theorem q16_63:ThresholdAt 16 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 63 0 (by decide +kernel)
  | exact S 16 63 1 (by decide +kernel)
  | exact S 16 63 2 (by decide +kernel)
  | exact S 16 63 3 (by decide +kernel)
  | exact S 16 63 4 (by decide +kernel)
  | exact S 16 63 5 (by decide +kernel)
theorem q16_64:ThresholdAt 16 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 64 0 (by decide +kernel)
  | exact S 16 64 1 (by decide +kernel)
  | exact S 16 64 2 (by decide +kernel)
  | exact S 16 64 3 (by decide +kernel)
  | exact S 16 64 4 (by decide +kernel)
  | exact S 16 64 5 (by decide +kernel)
theorem q16_65:ThresholdAt 16 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 65 0 (by decide +kernel)
  | exact S 16 65 1 (by decide +kernel)
  | exact S 16 65 2 (by decide +kernel)
  | exact S 16 65 3 (by decide +kernel)
  | exact S 16 65 4 (by decide +kernel)
  | exact S 16 65 5 (by decide +kernel)
theorem q16_66:ThresholdAt 16 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 66 0 (by decide +kernel)
  | exact S 16 66 1 (by decide +kernel)
  | exact S 16 66 2 (by decide +kernel)
  | exact S 16 66 3 (by decide +kernel)
  | exact S 16 66 4 (by decide +kernel)
  | exact S 16 66 5 (by decide +kernel)
theorem q16_67:ThresholdAt 16 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 67 0 (by decide +kernel)
  | exact S 16 67 1 (by decide +kernel)
  | exact S 16 67 2 (by decide +kernel)
  | exact S 16 67 3 (by decide +kernel)
  | exact S 16 67 4 (by decide +kernel)
  | exact S 16 67 5 (by decide +kernel)
theorem q16_68:ThresholdAt 16 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 68 0 (by decide +kernel)
  | exact S 16 68 1 (by decide +kernel)
  | exact S 16 68 2 (by decide +kernel)
  | exact S 16 68 3 (by decide +kernel)
  | exact S 16 68 4 (by decide +kernel)
  | exact S 16 68 5 (by decide +kernel)
theorem q16_69:ThresholdAt 16 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 69 0 (by decide +kernel)
  | exact S 16 69 1 (by decide +kernel)
  | exact S 16 69 2 (by decide +kernel)
  | exact S 16 69 3 (by decide +kernel)
  | exact S 16 69 4 (by decide +kernel)
  | exact S 16 69 5 (by decide +kernel)
theorem q16_70:ThresholdAt 16 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 70 0 (by decide +kernel)
  | exact S 16 70 1 (by decide +kernel)
  | exact S 16 70 2 (by decide +kernel)
  | exact S 16 70 3 (by decide +kernel)
  | exact S 16 70 4 (by decide +kernel)
  | exact S 16 70 5 (by decide +kernel)
theorem q16_71:ThresholdAt 16 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 71 0 (by decide +kernel)
  | exact S 16 71 1 (by decide +kernel)
  | exact S 16 71 2 (by decide +kernel)
  | exact S 16 71 3 (by decide +kernel)
  | exact S 16 71 4 (by decide +kernel)
  | exact S 16 71 5 (by decide +kernel)
theorem q16_72:ThresholdAt 16 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 72 0 (by decide +kernel)
  | exact S 16 72 1 (by decide +kernel)
  | exact S 16 72 2 (by decide +kernel)
  | exact S 16 72 3 (by decide +kernel)
  | exact S 16 72 4 (by decide +kernel)
  | exact S 16 72 5 (by decide +kernel)
theorem q16_73:ThresholdAt 16 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 73 0 (by decide +kernel)
  | exact S 16 73 1 (by decide +kernel)
  | exact S 16 73 2 (by decide +kernel)
  | exact S 16 73 3 (by decide +kernel)
  | exact S 16 73 4 (by decide +kernel)
  | exact S 16 73 5 (by decide +kernel)
theorem q16_74:ThresholdAt 16 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 74 0 (by decide +kernel)
  | exact S 16 74 1 (by decide +kernel)
  | exact S 16 74 2 (by decide +kernel)
  | exact S 16 74 3 (by decide +kernel)
  | exact S 16 74 4 (by decide +kernel)
  | exact S 16 74 5 (by decide +kernel)
theorem q16_75:ThresholdAt 16 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 75 0 (by decide +kernel)
  | exact S 16 75 1 (by decide +kernel)
  | exact S 16 75 2 (by decide +kernel)
  | exact S 16 75 3 (by decide +kernel)
  | exact S 16 75 4 (by decide +kernel)
  | exact S 16 75 5 (by decide +kernel)
theorem q16_76:ThresholdAt 16 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 76 0 (by decide +kernel)
  | exact S 16 76 1 (by decide +kernel)
  | exact S 16 76 2 (by decide +kernel)
  | exact S 16 76 3 (by decide +kernel)
  | exact S 16 76 4 (by decide +kernel)
  | exact S 16 76 5 (by decide +kernel)
theorem q16_77:ThresholdAt 16 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 77 0 (by decide +kernel)
  | exact S 16 77 1 (by decide +kernel)
  | exact S 16 77 2 (by decide +kernel)
  | exact S 16 77 3 (by decide +kernel)
  | exact S 16 77 4 (by decide +kernel)
  | exact S 16 77 5 (by decide +kernel)
theorem q16_78:ThresholdAt 16 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 78 0 (by decide +kernel)
  | exact S 16 78 1 (by decide +kernel)
  | exact S 16 78 2 (by decide +kernel)
  | exact S 16 78 3 (by decide +kernel)
  | exact S 16 78 4 (by decide +kernel)
  | exact S 16 78 5 (by decide +kernel)
theorem q16_79:ThresholdAt 16 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 79 0 (by decide +kernel)
  | exact S 16 79 1 (by decide +kernel)
  | exact S 16 79 2 (by decide +kernel)
  | exact S 16 79 3 (by decide +kernel)
  | exact S 16 79 4 (by decide +kernel)
  | exact S 16 79 5 (by decide +kernel)
theorem q16_80:ThresholdAt 16 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 80 0 (by decide +kernel)
  | exact S 16 80 1 (by decide +kernel)
  | exact S 16 80 2 (by decide +kernel)
  | exact S 16 80 3 (by decide +kernel)
  | exact S 16 80 4 (by decide +kernel)
  | exact S 16 80 5 (by decide +kernel)
theorem q16_81:ThresholdAt 16 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 81 0 (by decide +kernel)
  | exact S 16 81 1 (by decide +kernel)
  | exact S 16 81 2 (by decide +kernel)
  | exact S 16 81 3 (by decide +kernel)
  | exact S 16 81 4 (by decide +kernel)
  | exact S 16 81 5 (by decide +kernel)
theorem q16_82:ThresholdAt 16 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 82 0 (by decide +kernel)
  | exact S 16 82 1 (by decide +kernel)
  | exact S 16 82 2 (by decide +kernel)
  | exact S 16 82 3 (by decide +kernel)
  | exact S 16 82 4 (by decide +kernel)
  | exact S 16 82 5 (by decide +kernel)
theorem q16_83:ThresholdAt 16 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 83 0 (by decide +kernel)
  | exact S 16 83 1 (by decide +kernel)
  | exact S 16 83 2 (by decide +kernel)
  | exact S 16 83 3 (by decide +kernel)
  | exact S 16 83 4 (by decide +kernel)
  | exact S 16 83 5 (by decide +kernel)
theorem q16_84:ThresholdAt 16 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 84 0 (by decide +kernel)
  | exact S 16 84 1 (by decide +kernel)
  | exact S 16 84 2 (by decide +kernel)
  | exact S 16 84 3 (by decide +kernel)
  | exact S 16 84 4 (by decide +kernel)
  | exact S 16 84 5 (by decide +kernel)
theorem q16_85:ThresholdAt 16 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 85 0 (by decide +kernel)
  | exact S 16 85 1 (by decide +kernel)
  | exact S 16 85 2 (by decide +kernel)
  | exact S 16 85 3 (by decide +kernel)
  | exact S 16 85 4 (by decide +kernel)
  | exact S 16 85 5 (by decide +kernel)
theorem q16_86:ThresholdAt 16 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 86 0 (by decide +kernel)
  | exact S 16 86 1 (by decide +kernel)
  | exact S 16 86 2 (by decide +kernel)
  | exact S 16 86 3 (by decide +kernel)
  | exact S 16 86 4 (by decide +kernel)
  | exact S 16 86 5 (by decide +kernel)
theorem q16_87:ThresholdAt 16 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 87 0 (by decide +kernel)
  | exact S 16 87 1 (by decide +kernel)
  | exact S 16 87 2 (by decide +kernel)
  | exact S 16 87 3 (by decide +kernel)
  | exact S 16 87 4 (by decide +kernel)
  | exact S 16 87 5 (by decide +kernel)
theorem q16_88:ThresholdAt 16 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 88 0 (by decide +kernel)
  | exact S 16 88 1 (by decide +kernel)
  | exact S 16 88 2 (by decide +kernel)
  | exact S 16 88 3 (by decide +kernel)
  | exact S 16 88 4 (by decide +kernel)
  | exact S 16 88 5 (by decide +kernel)
theorem q16_89:ThresholdAt 16 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 89 0 (by decide +kernel)
  | exact S 16 89 1 (by decide +kernel)
  | exact S 16 89 2 (by decide +kernel)
  | exact S 16 89 3 (by decide +kernel)
  | exact S 16 89 4 (by decide +kernel)
  | exact S 16 89 5 (by decide +kernel)
theorem q16_90:ThresholdAt 16 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 90 0 (by decide +kernel)
  | exact S 16 90 1 (by decide +kernel)
  | exact S 16 90 2 (by decide +kernel)
  | exact S 16 90 3 (by decide +kernel)
  | exact S 16 90 4 (by decide +kernel)
  | exact S 16 90 5 (by decide +kernel)
theorem q16_91:ThresholdAt 16 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 91 0 (by decide +kernel)
  | exact S 16 91 1 (by decide +kernel)
  | exact S 16 91 2 (by decide +kernel)
  | exact S 16 91 3 (by decide +kernel)
  | exact S 16 91 4 (by decide +kernel)
  | exact S 16 91 5 (by decide +kernel)
theorem q16_92:ThresholdAt 16 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 92 0 (by decide +kernel)
  | exact S 16 92 1 (by decide +kernel)
  | exact S 16 92 2 (by decide +kernel)
  | exact S 16 92 3 (by decide +kernel)
  | exact S 16 92 4 (by decide +kernel)
  | exact S 16 92 5 (by decide +kernel)
theorem q16_93:ThresholdAt 16 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 93 0 (by decide +kernel)
  | exact S 16 93 1 (by decide +kernel)
  | exact S 16 93 2 (by decide +kernel)
  | exact S 16 93 3 (by decide +kernel)
  | exact S 16 93 4 (by decide +kernel)
  | exact S 16 93 5 (by decide +kernel)
theorem q16_94:ThresholdAt 16 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 94 0 (by decide +kernel)
  | exact S 16 94 1 (by decide +kernel)
  | exact S 16 94 2 (by decide +kernel)
  | exact S 16 94 3 (by decide +kernel)
  | exact S 16 94 4 (by decide +kernel)
  | exact S 16 94 5 (by decide +kernel)
theorem q16_95:ThresholdAt 16 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 95 0 (by decide +kernel)
  | exact S 16 95 1 (by decide +kernel)
  | exact S 16 95 2 (by decide +kernel)
  | exact S 16 95 3 (by decide +kernel)
  | exact S 16 95 4 (by decide +kernel)
  | exact S 16 95 5 (by decide +kernel)
theorem q16_96:ThresholdAt 16 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 96 0 (by decide +kernel)
  | exact S 16 96 1 (by decide +kernel)
  | exact S 16 96 2 (by decide +kernel)
  | exact S 16 96 3 (by decide +kernel)
  | exact S 16 96 4 (by decide +kernel)
  | exact S 16 96 5 (by decide +kernel)
theorem q16_97:ThresholdAt 16 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 97 0 (by decide +kernel)
  | exact S 16 97 1 (by decide +kernel)
  | exact S 16 97 2 (by decide +kernel)
  | exact S 16 97 3 (by decide +kernel)
  | exact S 16 97 4 (by decide +kernel)
  | exact S 16 97 5 (by decide +kernel)
theorem q16_98:ThresholdAt 16 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 98 0 (by decide +kernel)
  | exact S 16 98 1 (by decide +kernel)
  | exact S 16 98 2 (by decide +kernel)
  | exact S 16 98 3 (by decide +kernel)
  | exact S 16 98 4 (by decide +kernel)
  | exact S 16 98 5 (by decide +kernel)
theorem q16_99:ThresholdAt 16 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 99 0 (by decide +kernel)
  | exact S 16 99 1 (by decide +kernel)
  | exact S 16 99 2 (by decide +kernel)
  | exact S 16 99 3 (by decide +kernel)
  | exact S 16 99 4 (by decide +kernel)
  | exact S 16 99 5 (by decide +kernel)
theorem q16_100:ThresholdAt 16 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 100 0 (by decide +kernel)
  | exact S 16 100 1 (by decide +kernel)
  | exact S 16 100 2 (by decide +kernel)
  | exact S 16 100 3 (by decide +kernel)
  | exact S 16 100 4 (by decide +kernel)
  | exact S 16 100 5 (by decide +kernel)
theorem q16_101:ThresholdAt 16 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 101 0 (by decide +kernel)
  | exact S 16 101 1 (by decide +kernel)
  | exact S 16 101 2 (by decide +kernel)
  | exact S 16 101 3 (by decide +kernel)
  | exact S 16 101 4 (by decide +kernel)
  | exact S 16 101 5 (by decide +kernel)
theorem q16_102:ThresholdAt 16 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 102 0 (by decide +kernel)
  | exact S 16 102 1 (by decide +kernel)
  | exact S 16 102 2 (by decide +kernel)
  | exact S 16 102 3 (by decide +kernel)
  | exact S 16 102 4 (by decide +kernel)
  | exact S 16 102 5 (by decide +kernel)
theorem q16_103:ThresholdAt 16 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 103 0 (by decide +kernel)
  | exact S 16 103 1 (by decide +kernel)
  | exact S 16 103 2 (by decide +kernel)
  | exact S 16 103 3 (by decide +kernel)
  | exact S 16 103 4 (by decide +kernel)
  | exact S 16 103 5 (by decide +kernel)
theorem q16_104:ThresholdAt 16 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 104 0 (by decide +kernel)
  | exact S 16 104 1 (by decide +kernel)
  | exact S 16 104 2 (by decide +kernel)
  | exact S 16 104 3 (by decide +kernel)
  | exact S 16 104 4 (by decide +kernel)
  | exact S 16 104 5 (by decide +kernel)
theorem q16_105:ThresholdAt 16 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 105 0 (by decide +kernel)
  | exact S 16 105 1 (by decide +kernel)
  | exact S 16 105 2 (by decide +kernel)
  | exact S 16 105 3 (by decide +kernel)
  | exact S 16 105 4 (by decide +kernel)
  | exact S 16 105 5 (by decide +kernel)
theorem q16_106:ThresholdAt 16 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 106 0 (by decide +kernel)
  | exact S 16 106 1 (by decide +kernel)
  | exact S 16 106 2 (by decide +kernel)
  | exact S 16 106 3 (by decide +kernel)
  | exact S 16 106 4 (by decide +kernel)
  | exact S 16 106 5 (by decide +kernel)
theorem q16_107:ThresholdAt 16 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 107 0 (by decide +kernel)
  | exact S 16 107 1 (by decide +kernel)
  | exact S 16 107 2 (by decide +kernel)
  | exact S 16 107 3 (by decide +kernel)
  | exact S 16 107 4 (by decide +kernel)
  | exact S 16 107 5 (by decide +kernel)
theorem q16_108:ThresholdAt 16 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 108 0 (by decide +kernel)
  | exact S 16 108 1 (by decide +kernel)
  | exact S 16 108 2 (by decide +kernel)
  | exact S 16 108 3 (by decide +kernel)
  | exact S 16 108 4 (by decide +kernel)
  | exact S 16 108 5 (by decide +kernel)
theorem q16_109:ThresholdAt 16 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 109 0 (by decide +kernel)
  | exact S 16 109 1 (by decide +kernel)
  | exact S 16 109 2 (by decide +kernel)
  | exact S 16 109 3 (by decide +kernel)
  | exact S 16 109 4 (by decide +kernel)
  | exact S 16 109 5 (by decide +kernel)
theorem q16_110:ThresholdAt 16 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 110 0 (by decide +kernel)
  | exact S 16 110 1 (by decide +kernel)
  | exact S 16 110 2 (by decide +kernel)
  | exact S 16 110 3 (by decide +kernel)
  | exact S 16 110 4 (by decide +kernel)
  | exact S 16 110 5 (by decide +kernel)
theorem q16_111:ThresholdAt 16 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 111 0 (by decide +kernel)
  | exact S 16 111 1 (by decide +kernel)
  | exact S 16 111 2 (by decide +kernel)
  | exact S 16 111 3 (by decide +kernel)
  | exact S 16 111 4 (by decide +kernel)
  | exact S 16 111 5 (by decide +kernel)
theorem q16_112:ThresholdAt 16 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 112 0 (by decide +kernel)
  | exact S 16 112 1 (by decide +kernel)
  | exact S 16 112 2 (by decide +kernel)
  | exact S 16 112 3 (by decide +kernel)
  | exact S 16 112 4 (by decide +kernel)
  | exact S 16 112 5 (by decide +kernel)
theorem q16_113:ThresholdAt 16 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 113 0 (by decide +kernel)
  | exact S 16 113 1 (by decide +kernel)
  | exact S 16 113 2 (by decide +kernel)
  | exact S 16 113 3 (by decide +kernel)
  | exact S 16 113 4 (by decide +kernel)
  | exact S 16 113 5 (by decide +kernel)
theorem q16_114:ThresholdAt 16 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 114 0 (by decide +kernel)
  | exact S 16 114 1 (by decide +kernel)
  | exact S 16 114 2 (by decide +kernel)
  | exact S 16 114 3 (by decide +kernel)
  | exact S 16 114 4 (by decide +kernel)
  | exact S 16 114 5 (by decide +kernel)
theorem q16_115:ThresholdAt 16 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 115 0 (by decide +kernel)
  | exact S 16 115 1 (by decide +kernel)
  | exact S 16 115 2 (by decide +kernel)
  | exact S 16 115 3 (by decide +kernel)
  | exact S 16 115 4 (by decide +kernel)
  | exact S 16 115 5 (by decide +kernel)
theorem q16_116:ThresholdAt 16 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 116 0 (by decide +kernel)
  | exact S 16 116 1 (by decide +kernel)
  | exact S 16 116 2 (by decide +kernel)
  | exact S 16 116 3 (by decide +kernel)
  | exact S 16 116 4 (by decide +kernel)
  | exact S 16 116 5 (by decide +kernel)
theorem q16_117:ThresholdAt 16 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 117 0 (by decide +kernel)
  | exact S 16 117 1 (by decide +kernel)
  | exact S 16 117 2 (by decide +kernel)
  | exact S 16 117 3 (by decide +kernel)
  | exact S 16 117 4 (by decide +kernel)
  | exact S 16 117 5 (by decide +kernel)
theorem q16_118:ThresholdAt 16 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 118 0 (by decide +kernel)
  | exact S 16 118 1 (by decide +kernel)
  | exact S 16 118 2 (by decide +kernel)
  | exact S 16 118 3 (by decide +kernel)
  | exact S 16 118 4 (by decide +kernel)
  | exact S 16 118 5 (by decide +kernel)
theorem q16_119:ThresholdAt 16 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 119 0 (by decide +kernel)
  | exact S 16 119 1 (by decide +kernel)
  | exact S 16 119 2 (by decide +kernel)
  | exact S 16 119 3 (by decide +kernel)
  | exact S 16 119 4 (by decide +kernel)
  | exact S 16 119 5 (by decide +kernel)
theorem q16_120:ThresholdAt 16 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 120 0 (by decide +kernel)
  | exact S 16 120 1 (by decide +kernel)
  | exact S 16 120 2 (by decide +kernel)
  | exact S 16 120 3 (by decide +kernel)
  | exact S 16 120 4 (by decide +kernel)
  | exact S 16 120 5 (by decide +kernel)
theorem q16_121:ThresholdAt 16 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 121 0 (by decide +kernel)
  | exact S 16 121 1 (by decide +kernel)
  | exact S 16 121 2 (by decide +kernel)
  | exact S 16 121 3 (by decide +kernel)
  | exact S 16 121 4 (by decide +kernel)
  | exact S 16 121 5 (by decide +kernel)
theorem q16_122:ThresholdAt 16 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 122 0 (by decide +kernel)
  | exact S 16 122 1 (by decide +kernel)
  | exact S 16 122 2 (by decide +kernel)
  | exact S 16 122 3 (by decide +kernel)
  | exact S 16 122 4 (by decide +kernel)
  | exact S 16 122 5 (by decide +kernel)
theorem q16_123:ThresholdAt 16 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 123 0 (by decide +kernel)
  | exact S 16 123 1 (by decide +kernel)
  | exact S 16 123 2 (by decide +kernel)
  | exact S 16 123 3 (by decide +kernel)
  | exact S 16 123 4 (by decide +kernel)
  | exact S 16 123 5 (by decide +kernel)
theorem q16_124:ThresholdAt 16 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 124 0 (by decide +kernel)
  | exact S 16 124 1 (by decide +kernel)
  | exact S 16 124 2 (by decide +kernel)
  | exact S 16 124 3 (by decide +kernel)
  | exact S 16 124 4 (by decide +kernel)
  | exact S 16 124 5 (by decide +kernel)
theorem q16_125:ThresholdAt 16 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 125 0 (by decide +kernel)
  | exact S 16 125 1 (by decide +kernel)
  | exact S 16 125 2 (by decide +kernel)
  | exact S 16 125 3 (by decide +kernel)
  | exact S 16 125 4 (by decide +kernel)
  | exact S 16 125 5 (by decide +kernel)
theorem q16_126:ThresholdAt 16 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 126 0 (by decide +kernel)
  | exact S 16 126 1 (by decide +kernel)
  | exact S 16 126 2 (by decide +kernel)
  | exact S 16 126 3 (by decide +kernel)
  | exact S 16 126 4 (by decide +kernel)
  | exact S 16 126 5 (by decide +kernel)
theorem checkedR16:∀ V ∈ List.range 127,ThresholdAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0_127:V < 63
  · by_cases h0_63:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q16_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q16_1
              · have he:V = 2:=by omega
                subst V
                exact q16_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q16_3
              · have he:V = 4:=by omega
                subst V
                exact q16_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q16_5
              · have he:V = 6:=by omega
                subst V
                exact q16_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q16_7
              · have he:V = 8:=by omega
                subst V
                exact q16_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q16_9
              · have he:V = 10:=by omega
                subst V
                exact q16_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q16_11
              · have he:V = 12:=by omega
                subst V
                exact q16_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q16_13
              · have he:V = 14:=by omega
                subst V
                exact q16_14
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q16_15
              · have he:V = 16:=by omega
                subst V
                exact q16_16
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q16_17
              · have he:V = 18:=by omega
                subst V
                exact q16_18
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q16_19
              · have he:V = 20:=by omega
                subst V
                exact q16_20
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q16_21
              · have he:V = 22:=by omega
                subst V
                exact q16_22
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q16_23
              · have he:V = 24:=by omega
                subst V
                exact q16_24
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q16_25
              · have he:V = 26:=by omega
                subst V
                exact q16_26
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q16_27
              · have he:V = 28:=by omega
                subst V
                exact q16_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q16_29
              · have he:V = 30:=by omega
                subst V
                exact q16_30
    · by_cases h31_63:V < 47
      · by_cases h31_47:V < 39
        · by_cases h31_39:V < 35
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q16_31
              · have he:V = 32:=by omega
                subst V
                exact q16_32
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q16_33
              · have he:V = 34:=by omega
                subst V
                exact q16_34
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q16_35
              · have he:V = 36:=by omega
                subst V
                exact q16_36
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q16_37
              · have he:V = 38:=by omega
                subst V
                exact q16_38
        · by_cases h39_47:V < 43
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q16_39
              · have he:V = 40:=by omega
                subst V
                exact q16_40
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q16_41
              · have he:V = 42:=by omega
                subst V
                exact q16_42
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q16_43
              · have he:V = 44:=by omega
                subst V
                exact q16_44
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q16_45
              · have he:V = 46:=by omega
                subst V
                exact q16_46
      · by_cases h47_63:V < 55
        · by_cases h47_55:V < 51
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q16_47
              · have he:V = 48:=by omega
                subst V
                exact q16_48
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q16_49
              · have he:V = 50:=by omega
                subst V
                exact q16_50
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q16_51
              · have he:V = 52:=by omega
                subst V
                exact q16_52
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q16_53
              · have he:V = 54:=by omega
                subst V
                exact q16_54
        · by_cases h55_63:V < 59
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q16_55
              · have he:V = 56:=by omega
                subst V
                exact q16_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q16_57
              · have he:V = 58:=by omega
                subst V
                exact q16_58
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q16_59
              · have he:V = 60:=by omega
                subst V
                exact q16_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q16_61
              · have he:V = 62:=by omega
                subst V
                exact q16_62
  · by_cases h63_127:V < 95
    · by_cases h63_95:V < 79
      · by_cases h63_79:V < 71
        · by_cases h63_71:V < 67
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q16_63
              · have he:V = 64:=by omega
                subst V
                exact q16_64
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q16_65
              · have he:V = 66:=by omega
                subst V
                exact q16_66
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q16_67
              · have he:V = 68:=by omega
                subst V
                exact q16_68
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q16_69
              · have he:V = 70:=by omega
                subst V
                exact q16_70
        · by_cases h71_79:V < 75
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q16_71
              · have he:V = 72:=by omega
                subst V
                exact q16_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q16_73
              · have he:V = 74:=by omega
                subst V
                exact q16_74
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q16_75
              · have he:V = 76:=by omega
                subst V
                exact q16_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q16_77
              · have he:V = 78:=by omega
                subst V
                exact q16_78
      · by_cases h79_95:V < 87
        · by_cases h79_87:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q16_79
              · have he:V = 80:=by omega
                subst V
                exact q16_80
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q16_81
              · have he:V = 82:=by omega
                subst V
                exact q16_82
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q16_83
              · have he:V = 84:=by omega
                subst V
                exact q16_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q16_85
              · have he:V = 86:=by omega
                subst V
                exact q16_86
        · by_cases h87_95:V < 91
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q16_87
              · have he:V = 88:=by omega
                subst V
                exact q16_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q16_89
              · have he:V = 90:=by omega
                subst V
                exact q16_90
          · by_cases h91_95:V < 93
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q16_91
              · have he:V = 92:=by omega
                subst V
                exact q16_92
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q16_93
              · have he:V = 94:=by omega
                subst V
                exact q16_94
    · by_cases h95_127:V < 111
      · by_cases h95_111:V < 103
        · by_cases h95_103:V < 99
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q16_95
              · have he:V = 96:=by omega
                subst V
                exact q16_96
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q16_97
              · have he:V = 98:=by omega
                subst V
                exact q16_98
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q16_99
              · have he:V = 100:=by omega
                subst V
                exact q16_100
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q16_101
              · have he:V = 102:=by omega
                subst V
                exact q16_102
        · by_cases h103_111:V < 107
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q16_103
              · have he:V = 104:=by omega
                subst V
                exact q16_104
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q16_105
              · have he:V = 106:=by omega
                subst V
                exact q16_106
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q16_107
              · have he:V = 108:=by omega
                subst V
                exact q16_108
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q16_109
              · have he:V = 110:=by omega
                subst V
                exact q16_110
      · by_cases h111_127:V < 119
        · by_cases h111_119:V < 115
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q16_111
              · have he:V = 112:=by omega
                subst V
                exact q16_112
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q16_113
              · have he:V = 114:=by omega
                subst V
                exact q16_114
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q16_115
              · have he:V = 116:=by omega
                subst V
                exact q16_116
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q16_117
              · have he:V = 118:=by omega
                subst V
                exact q16_118
        · by_cases h119_127:V < 123
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q16_119
              · have he:V = 120:=by omega
                subst V
                exact q16_120
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q16_121
              · have he:V = 122:=by omega
                subst V
                exact q16_122
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q16_123
              · have he:V = 124:=by omega
                subst V
                exact q16_124
            · by_cases h125_127:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q16_125
              · have he:V = 126:=by omega
                subst V
                exact q16_126
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
