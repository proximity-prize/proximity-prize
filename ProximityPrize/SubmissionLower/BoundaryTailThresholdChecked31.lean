import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked30

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q31_0:ThresholdAt 31 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 0 0 (by decide +kernel)
  | exact S 31 0 1 (by decide +kernel)
  | exact S 31 0 2 (by decide +kernel)
  | exact S 31 0 3 (by decide +kernel)
  | exact S 31 0 4 (by decide +kernel)
  | exact S 31 0 5 (by decide +kernel)
theorem q31_1:ThresholdAt 31 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 1 0 (by decide +kernel)
  | exact S 31 1 1 (by decide +kernel)
  | exact S 31 1 2 (by decide +kernel)
  | exact S 31 1 3 (by decide +kernel)
  | exact S 31 1 4 (by decide +kernel)
  | exact S 31 1 5 (by decide +kernel)
theorem q31_2:ThresholdAt 31 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 2 0 (by decide +kernel)
  | exact S 31 2 1 (by decide +kernel)
  | exact S 31 2 2 (by decide +kernel)
  | exact S 31 2 3 (by decide +kernel)
  | exact S 31 2 4 (by decide +kernel)
  | exact S 31 2 5 (by decide +kernel)
theorem q31_3:ThresholdAt 31 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 3 0 (by decide +kernel)
  | exact S 31 3 1 (by decide +kernel)
  | exact S 31 3 2 (by decide +kernel)
  | exact S 31 3 3 (by decide +kernel)
  | exact S 31 3 4 (by decide +kernel)
  | exact S 31 3 5 (by decide +kernel)
theorem q31_4:ThresholdAt 31 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 4 0 (by decide +kernel)
  | exact S 31 4 1 (by decide +kernel)
  | exact S 31 4 2 (by decide +kernel)
  | exact S 31 4 3 (by decide +kernel)
  | exact S 31 4 4 (by decide +kernel)
  | exact S 31 4 5 (by decide +kernel)
theorem q31_5:ThresholdAt 31 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 5 0 (by decide +kernel)
  | exact S 31 5 1 (by decide +kernel)
  | exact S 31 5 2 (by decide +kernel)
  | exact S 31 5 3 (by decide +kernel)
  | exact S 31 5 4 (by decide +kernel)
  | exact S 31 5 5 (by decide +kernel)
theorem q31_6:ThresholdAt 31 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 6 0 (by decide +kernel)
  | exact S 31 6 1 (by decide +kernel)
  | exact S 31 6 2 (by decide +kernel)
  | exact S 31 6 3 (by decide +kernel)
  | exact S 31 6 4 (by decide +kernel)
  | exact S 31 6 5 (by decide +kernel)
theorem q31_7:ThresholdAt 31 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 7 0 (by decide +kernel)
  | exact S 31 7 1 (by decide +kernel)
  | exact S 31 7 2 (by decide +kernel)
  | exact S 31 7 3 (by decide +kernel)
  | exact S 31 7 4 (by decide +kernel)
  | exact S 31 7 5 (by decide +kernel)
theorem q31_8:ThresholdAt 31 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 8 0 (by decide +kernel)
  | exact S 31 8 1 (by decide +kernel)
  | exact S 31 8 2 (by decide +kernel)
  | exact S 31 8 3 (by decide +kernel)
  | exact S 31 8 4 (by decide +kernel)
  | exact S 31 8 5 (by decide +kernel)
theorem q31_9:ThresholdAt 31 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 9 0 (by decide +kernel)
  | exact S 31 9 1 (by decide +kernel)
  | exact S 31 9 2 (by decide +kernel)
  | exact S 31 9 3 (by decide +kernel)
  | exact S 31 9 4 (by decide +kernel)
  | exact S 31 9 5 (by decide +kernel)
theorem q31_10:ThresholdAt 31 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 10 0 (by decide +kernel)
  | exact S 31 10 1 (by decide +kernel)
  | exact S 31 10 2 (by decide +kernel)
  | exact S 31 10 3 (by decide +kernel)
  | exact S 31 10 4 (by decide +kernel)
  | exact S 31 10 5 (by decide +kernel)
theorem q31_11:ThresholdAt 31 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 11 0 (by decide +kernel)
  | exact S 31 11 1 (by decide +kernel)
  | exact S 31 11 2 (by decide +kernel)
  | exact S 31 11 3 (by decide +kernel)
  | exact S 31 11 4 (by decide +kernel)
  | exact S 31 11 5 (by decide +kernel)
theorem q31_12:ThresholdAt 31 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 12 0 (by decide +kernel)
  | exact S 31 12 1 (by decide +kernel)
  | exact S 31 12 2 (by decide +kernel)
  | exact S 31 12 3 (by decide +kernel)
  | exact S 31 12 4 (by decide +kernel)
  | exact S 31 12 5 (by decide +kernel)
theorem q31_13:ThresholdAt 31 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 13 0 (by decide +kernel)
  | exact S 31 13 1 (by decide +kernel)
  | exact S 31 13 2 (by decide +kernel)
  | exact S 31 13 3 (by decide +kernel)
  | exact S 31 13 4 (by decide +kernel)
  | exact S 31 13 5 (by decide +kernel)
theorem q31_14:ThresholdAt 31 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 14 0 (by decide +kernel)
  | exact S 31 14 1 (by decide +kernel)
  | exact S 31 14 2 (by decide +kernel)
  | exact S 31 14 3 (by decide +kernel)
  | exact S 31 14 4 (by decide +kernel)
  | exact S 31 14 5 (by decide +kernel)
theorem q31_15:ThresholdAt 31 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 15 0 (by decide +kernel)
  | exact S 31 15 1 (by decide +kernel)
  | exact S 31 15 2 (by decide +kernel)
  | exact S 31 15 3 (by decide +kernel)
  | exact S 31 15 4 (by decide +kernel)
  | exact S 31 15 5 (by decide +kernel)
theorem q31_16:ThresholdAt 31 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 16 0 (by decide +kernel)
  | exact S 31 16 1 (by decide +kernel)
  | exact S 31 16 2 (by decide +kernel)
  | exact S 31 16 3 (by decide +kernel)
  | exact S 31 16 4 (by decide +kernel)
  | exact S 31 16 5 (by decide +kernel)
theorem q31_17:ThresholdAt 31 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 17 0 (by decide +kernel)
  | exact S 31 17 1 (by decide +kernel)
  | exact S 31 17 2 (by decide +kernel)
  | exact S 31 17 3 (by decide +kernel)
  | exact S 31 17 4 (by decide +kernel)
  | exact S 31 17 5 (by decide +kernel)
theorem q31_18:ThresholdAt 31 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 18 0 (by decide +kernel)
  | exact S 31 18 1 (by decide +kernel)
  | exact S 31 18 2 (by decide +kernel)
  | exact S 31 18 3 (by decide +kernel)
  | exact S 31 18 4 (by decide +kernel)
  | exact S 31 18 5 (by decide +kernel)
theorem q31_19:ThresholdAt 31 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 19 0 (by decide +kernel)
  | exact S 31 19 1 (by decide +kernel)
  | exact S 31 19 2 (by decide +kernel)
  | exact S 31 19 3 (by decide +kernel)
  | exact S 31 19 4 (by decide +kernel)
  | exact S 31 19 5 (by decide +kernel)
theorem q31_20:ThresholdAt 31 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 20 0 (by decide +kernel)
  | exact S 31 20 1 (by decide +kernel)
  | exact S 31 20 2 (by decide +kernel)
  | exact S 31 20 3 (by decide +kernel)
  | exact S 31 20 4 (by decide +kernel)
  | exact S 31 20 5 (by decide +kernel)
theorem q31_21:ThresholdAt 31 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 21 0 (by decide +kernel)
  | exact S 31 21 1 (by decide +kernel)
  | exact S 31 21 2 (by decide +kernel)
  | exact S 31 21 3 (by decide +kernel)
  | exact S 31 21 4 (by decide +kernel)
  | exact S 31 21 5 (by decide +kernel)
theorem q31_22:ThresholdAt 31 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 22 0 (by decide +kernel)
  | exact S 31 22 1 (by decide +kernel)
  | exact S 31 22 2 (by decide +kernel)
  | exact S 31 22 3 (by decide +kernel)
  | exact S 31 22 4 (by decide +kernel)
  | exact S 31 22 5 (by decide +kernel)
theorem q31_23:ThresholdAt 31 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 23 0 (by decide +kernel)
  | exact S 31 23 1 (by decide +kernel)
  | exact S 31 23 2 (by decide +kernel)
  | exact S 31 23 3 (by decide +kernel)
  | exact S 31 23 4 (by decide +kernel)
  | exact S 31 23 5 (by decide +kernel)
theorem q31_24:ThresholdAt 31 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 24 0 (by decide +kernel)
  | exact S 31 24 1 (by decide +kernel)
  | exact S 31 24 2 (by decide +kernel)
  | exact S 31 24 3 (by decide +kernel)
  | exact S 31 24 4 (by decide +kernel)
  | exact S 31 24 5 (by decide +kernel)
theorem q31_25:ThresholdAt 31 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 25 0 (by decide +kernel)
  | exact S 31 25 1 (by decide +kernel)
  | exact S 31 25 2 (by decide +kernel)
  | exact S 31 25 3 (by decide +kernel)
  | exact S 31 25 4 (by decide +kernel)
  | exact S 31 25 5 (by decide +kernel)
theorem q31_26:ThresholdAt 31 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 26 0 (by decide +kernel)
  | exact S 31 26 1 (by decide +kernel)
  | exact S 31 26 2 (by decide +kernel)
  | exact S 31 26 3 (by decide +kernel)
  | exact S 31 26 4 (by decide +kernel)
  | exact S 31 26 5 (by decide +kernel)
theorem q31_27:ThresholdAt 31 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 27 0 (by decide +kernel)
  | exact S 31 27 1 (by decide +kernel)
  | exact S 31 27 2 (by decide +kernel)
  | exact S 31 27 3 (by decide +kernel)
  | exact S 31 27 4 (by decide +kernel)
  | exact S 31 27 5 (by decide +kernel)
theorem q31_28:ThresholdAt 31 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 28 0 (by decide +kernel)
  | exact S 31 28 1 (by decide +kernel)
  | exact S 31 28 2 (by decide +kernel)
  | exact S 31 28 3 (by decide +kernel)
  | exact S 31 28 4 (by decide +kernel)
  | exact S 31 28 5 (by decide +kernel)
theorem q31_29:ThresholdAt 31 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 29 0 (by decide +kernel)
  | exact S 31 29 1 (by decide +kernel)
  | exact S 31 29 2 (by decide +kernel)
  | exact S 31 29 3 (by decide +kernel)
  | exact S 31 29 4 (by decide +kernel)
  | exact S 31 29 5 (by decide +kernel)
theorem q31_30:ThresholdAt 31 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 30 0 (by decide +kernel)
  | exact S 31 30 1 (by decide +kernel)
  | exact S 31 30 2 (by decide +kernel)
  | exact S 31 30 3 (by decide +kernel)
  | exact S 31 30 4 (by decide +kernel)
  | exact S 31 30 5 (by decide +kernel)
theorem q31_31:ThresholdAt 31 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 31 0 (by decide +kernel)
  | exact S 31 31 1 (by decide +kernel)
  | exact S 31 31 2 (by decide +kernel)
  | exact S 31 31 3 (by decide +kernel)
  | exact S 31 31 4 (by decide +kernel)
  | exact S 31 31 5 (by decide +kernel)
theorem q31_32:ThresholdAt 31 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 32 0 (by decide +kernel)
  | exact S 31 32 1 (by decide +kernel)
  | exact S 31 32 2 (by decide +kernel)
  | exact S 31 32 3 (by decide +kernel)
  | exact S 31 32 4 (by decide +kernel)
  | exact S 31 32 5 (by decide +kernel)
theorem q31_33:ThresholdAt 31 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 33 0 (by decide +kernel)
  | exact S 31 33 1 (by decide +kernel)
  | exact S 31 33 2 (by decide +kernel)
  | exact S 31 33 3 (by decide +kernel)
  | exact S 31 33 4 (by decide +kernel)
  | exact S 31 33 5 (by decide +kernel)
theorem q31_34:ThresholdAt 31 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 34 0 (by decide +kernel)
  | exact S 31 34 1 (by decide +kernel)
  | exact S 31 34 2 (by decide +kernel)
  | exact S 31 34 3 (by decide +kernel)
  | exact S 31 34 4 (by decide +kernel)
  | exact S 31 34 5 (by decide +kernel)
theorem q31_35:ThresholdAt 31 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 35 0 (by decide +kernel)
  | exact S 31 35 1 (by decide +kernel)
  | exact S 31 35 2 (by decide +kernel)
  | exact S 31 35 3 (by decide +kernel)
  | exact S 31 35 4 (by decide +kernel)
  | exact S 31 35 5 (by decide +kernel)
theorem q31_36:ThresholdAt 31 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 36 0 (by decide +kernel)
  | exact S 31 36 1 (by decide +kernel)
  | exact S 31 36 2 (by decide +kernel)
  | exact S 31 36 3 (by decide +kernel)
  | exact S 31 36 4 (by decide +kernel)
  | exact S 31 36 5 (by decide +kernel)
theorem q31_37:ThresholdAt 31 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 37 0 (by decide +kernel)
  | exact S 31 37 1 (by decide +kernel)
  | exact S 31 37 2 (by decide +kernel)
  | exact S 31 37 3 (by decide +kernel)
  | exact S 31 37 4 (by decide +kernel)
  | exact S 31 37 5 (by decide +kernel)
theorem q31_38:ThresholdAt 31 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 38 0 (by decide +kernel)
  | exact S 31 38 1 (by decide +kernel)
  | exact S 31 38 2 (by decide +kernel)
  | exact S 31 38 3 (by decide +kernel)
  | exact S 31 38 4 (by decide +kernel)
  | exact S 31 38 5 (by decide +kernel)
theorem q31_39:ThresholdAt 31 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 39 0 (by decide +kernel)
  | exact S 31 39 1 (by decide +kernel)
  | exact S 31 39 2 (by decide +kernel)
  | exact S 31 39 3 (by decide +kernel)
  | exact S 31 39 4 (by decide +kernel)
  | exact S 31 39 5 (by decide +kernel)
theorem q31_40:ThresholdAt 31 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 40 0 (by decide +kernel)
  | exact S 31 40 1 (by decide +kernel)
  | exact S 31 40 2 (by decide +kernel)
  | exact S 31 40 3 (by decide +kernel)
  | exact S 31 40 4 (by decide +kernel)
  | exact S 31 40 5 (by decide +kernel)
theorem q31_41:ThresholdAt 31 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 41 0 (by decide +kernel)
  | exact S 31 41 1 (by decide +kernel)
  | exact S 31 41 2 (by decide +kernel)
  | exact S 31 41 3 (by decide +kernel)
  | exact S 31 41 4 (by decide +kernel)
  | exact S 31 41 5 (by decide +kernel)
theorem q31_42:ThresholdAt 31 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 42 0 (by decide +kernel)
  | exact S 31 42 1 (by decide +kernel)
  | exact S 31 42 2 (by decide +kernel)
  | exact S 31 42 3 (by decide +kernel)
  | exact S 31 42 4 (by decide +kernel)
  | exact S 31 42 5 (by decide +kernel)
theorem q31_43:ThresholdAt 31 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 43 0 (by decide +kernel)
  | exact S 31 43 1 (by decide +kernel)
  | exact S 31 43 2 (by decide +kernel)
  | exact S 31 43 3 (by decide +kernel)
  | exact S 31 43 4 (by decide +kernel)
  | exact S 31 43 5 (by decide +kernel)
theorem q31_44:ThresholdAt 31 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 44 0 (by decide +kernel)
  | exact S 31 44 1 (by decide +kernel)
  | exact S 31 44 2 (by decide +kernel)
  | exact S 31 44 3 (by decide +kernel)
  | exact S 31 44 4 (by decide +kernel)
  | exact S 31 44 5 (by decide +kernel)
theorem q31_45:ThresholdAt 31 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 45 0 (by decide +kernel)
  | exact S 31 45 1 (by decide +kernel)
  | exact S 31 45 2 (by decide +kernel)
  | exact S 31 45 3 (by decide +kernel)
  | exact S 31 45 4 (by decide +kernel)
  | exact S 31 45 5 (by decide +kernel)
theorem q31_46:ThresholdAt 31 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 46 0 (by decide +kernel)
  | exact S 31 46 1 (by decide +kernel)
  | exact S 31 46 2 (by decide +kernel)
  | exact S 31 46 3 (by decide +kernel)
  | exact S 31 46 4 (by decide +kernel)
  | exact S 31 46 5 (by decide +kernel)
theorem q31_47:ThresholdAt 31 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 47 0 (by decide +kernel)
  | exact S 31 47 1 (by decide +kernel)
  | exact S 31 47 2 (by decide +kernel)
  | exact S 31 47 3 (by decide +kernel)
  | exact S 31 47 4 (by decide +kernel)
  | exact S 31 47 5 (by decide +kernel)
theorem q31_48:ThresholdAt 31 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 48 0 (by decide +kernel)
  | exact S 31 48 1 (by decide +kernel)
  | exact S 31 48 2 (by decide +kernel)
  | exact S 31 48 3 (by decide +kernel)
  | exact S 31 48 4 (by decide +kernel)
  | exact S 31 48 5 (by decide +kernel)
theorem q31_49:ThresholdAt 31 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 49 0 (by decide +kernel)
  | exact S 31 49 1 (by decide +kernel)
  | exact S 31 49 2 (by decide +kernel)
  | exact S 31 49 3 (by decide +kernel)
  | exact S 31 49 4 (by decide +kernel)
  | exact S 31 49 5 (by decide +kernel)
theorem q31_50:ThresholdAt 31 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 50 0 (by decide +kernel)
  | exact S 31 50 1 (by decide +kernel)
  | exact S 31 50 2 (by decide +kernel)
  | exact S 31 50 3 (by decide +kernel)
  | exact S 31 50 4 (by decide +kernel)
  | exact S 31 50 5 (by decide +kernel)
theorem q31_51:ThresholdAt 31 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 51 0 (by decide +kernel)
  | exact S 31 51 1 (by decide +kernel)
  | exact S 31 51 2 (by decide +kernel)
  | exact S 31 51 3 (by decide +kernel)
  | exact S 31 51 4 (by decide +kernel)
  | exact S 31 51 5 (by decide +kernel)
theorem q31_52:ThresholdAt 31 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 52 0 (by decide +kernel)
  | exact S 31 52 1 (by decide +kernel)
  | exact S 31 52 2 (by decide +kernel)
  | exact S 31 52 3 (by decide +kernel)
  | exact S 31 52 4 (by decide +kernel)
  | exact S 31 52 5 (by decide +kernel)
theorem q31_53:ThresholdAt 31 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 53 0 (by decide +kernel)
  | exact S 31 53 1 (by decide +kernel)
  | exact S 31 53 2 (by decide +kernel)
  | exact S 31 53 3 (by decide +kernel)
  | exact S 31 53 4 (by decide +kernel)
  | exact S 31 53 5 (by decide +kernel)
theorem q31_54:ThresholdAt 31 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 54 0 (by decide +kernel)
  | exact S 31 54 1 (by decide +kernel)
  | exact S 31 54 2 (by decide +kernel)
  | exact S 31 54 3 (by decide +kernel)
  | exact S 31 54 4 (by decide +kernel)
  | exact S 31 54 5 (by decide +kernel)
theorem q31_55:ThresholdAt 31 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 55 0 (by decide +kernel)
  | exact S 31 55 1 (by decide +kernel)
  | exact S 31 55 2 (by decide +kernel)
  | exact S 31 55 3 (by decide +kernel)
  | exact S 31 55 4 (by decide +kernel)
  | exact S 31 55 5 (by decide +kernel)
theorem q31_56:ThresholdAt 31 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 56 0 (by decide +kernel)
  | exact S 31 56 1 (by decide +kernel)
  | exact S 31 56 2 (by decide +kernel)
  | exact S 31 56 3 (by decide +kernel)
  | exact S 31 56 4 (by decide +kernel)
  | exact S 31 56 5 (by decide +kernel)
theorem q31_57:ThresholdAt 31 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 57 0 (by decide +kernel)
  | exact S 31 57 1 (by decide +kernel)
  | exact S 31 57 2 (by decide +kernel)
  | exact S 31 57 3 (by decide +kernel)
  | exact S 31 57 4 (by decide +kernel)
  | exact S 31 57 5 (by decide +kernel)
theorem q31_58:ThresholdAt 31 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 58 0 (by decide +kernel)
  | exact S 31 58 1 (by decide +kernel)
  | exact S 31 58 2 (by decide +kernel)
  | exact S 31 58 3 (by decide +kernel)
  | exact S 31 58 4 (by decide +kernel)
  | exact S 31 58 5 (by decide +kernel)
theorem q31_59:ThresholdAt 31 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 59 0 (by decide +kernel)
  | exact S 31 59 1 (by decide +kernel)
  | exact S 31 59 2 (by decide +kernel)
  | exact S 31 59 3 (by decide +kernel)
  | exact S 31 59 4 (by decide +kernel)
  | exact S 31 59 5 (by decide +kernel)
theorem q31_60:ThresholdAt 31 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 60 0 (by decide +kernel)
  | exact S 31 60 1 (by decide +kernel)
  | exact S 31 60 2 (by decide +kernel)
  | exact S 31 60 3 (by decide +kernel)
  | exact S 31 60 4 (by decide +kernel)
  | exact S 31 60 5 (by decide +kernel)
theorem q31_61:ThresholdAt 31 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 61 0 (by decide +kernel)
  | exact S 31 61 1 (by decide +kernel)
  | exact S 31 61 2 (by decide +kernel)
  | exact S 31 61 3 (by decide +kernel)
  | exact S 31 61 4 (by decide +kernel)
  | exact S 31 61 5 (by decide +kernel)
theorem q31_62:ThresholdAt 31 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 62 0 (by decide +kernel)
  | exact S 31 62 1 (by decide +kernel)
  | exact S 31 62 2 (by decide +kernel)
  | exact S 31 62 3 (by decide +kernel)
  | exact S 31 62 4 (by decide +kernel)
  | exact S 31 62 5 (by decide +kernel)
theorem q31_63:ThresholdAt 31 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 63 0 (by decide +kernel)
  | exact S 31 63 1 (by decide +kernel)
  | exact S 31 63 2 (by decide +kernel)
  | exact S 31 63 3 (by decide +kernel)
  | exact S 31 63 4 (by decide +kernel)
  | exact S 31 63 5 (by decide +kernel)
theorem q31_64:ThresholdAt 31 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 64 0 (by decide +kernel)
  | exact S 31 64 1 (by decide +kernel)
  | exact S 31 64 2 (by decide +kernel)
  | exact S 31 64 3 (by decide +kernel)
  | exact S 31 64 4 (by decide +kernel)
  | exact S 31 64 5 (by decide +kernel)
theorem q31_65:ThresholdAt 31 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 65 0 (by decide +kernel)
  | exact S 31 65 1 (by decide +kernel)
  | exact S 31 65 2 (by decide +kernel)
  | exact S 31 65 3 (by decide +kernel)
  | exact S 31 65 4 (by decide +kernel)
  | exact S 31 65 5 (by decide +kernel)
theorem q31_66:ThresholdAt 31 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 66 0 (by decide +kernel)
  | exact S 31 66 1 (by decide +kernel)
  | exact S 31 66 2 (by decide +kernel)
  | exact S 31 66 3 (by decide +kernel)
  | exact S 31 66 4 (by decide +kernel)
  | exact S 31 66 5 (by decide +kernel)
theorem q31_67:ThresholdAt 31 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 67 0 (by decide +kernel)
  | exact S 31 67 1 (by decide +kernel)
  | exact S 31 67 2 (by decide +kernel)
  | exact S 31 67 3 (by decide +kernel)
  | exact S 31 67 4 (by decide +kernel)
  | exact S 31 67 5 (by decide +kernel)
theorem q31_68:ThresholdAt 31 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 68 0 (by decide +kernel)
  | exact S 31 68 1 (by decide +kernel)
  | exact S 31 68 2 (by decide +kernel)
  | exact S 31 68 3 (by decide +kernel)
  | exact S 31 68 4 (by decide +kernel)
  | exact S 31 68 5 (by decide +kernel)
theorem q31_69:ThresholdAt 31 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 69 0 (by decide +kernel)
  | exact S 31 69 1 (by decide +kernel)
  | exact S 31 69 2 (by decide +kernel)
  | exact S 31 69 3 (by decide +kernel)
  | exact S 31 69 4 (by decide +kernel)
  | exact S 31 69 5 (by decide +kernel)
theorem q31_70:ThresholdAt 31 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 70 0 (by decide +kernel)
  | exact S 31 70 1 (by decide +kernel)
  | exact S 31 70 2 (by decide +kernel)
  | exact S 31 70 3 (by decide +kernel)
  | exact S 31 70 4 (by decide +kernel)
  | exact S 31 70 5 (by decide +kernel)
theorem q31_71:ThresholdAt 31 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 71 0 (by decide +kernel)
  | exact S 31 71 1 (by decide +kernel)
  | exact S 31 71 2 (by decide +kernel)
  | exact S 31 71 3 (by decide +kernel)
  | exact S 31 71 4 (by decide +kernel)
  | exact S 31 71 5 (by decide +kernel)
theorem q31_72:ThresholdAt 31 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 72 0 (by decide +kernel)
  | exact S 31 72 1 (by decide +kernel)
  | exact S 31 72 2 (by decide +kernel)
  | exact S 31 72 3 (by decide +kernel)
  | exact S 31 72 4 (by decide +kernel)
  | exact S 31 72 5 (by decide +kernel)
theorem q31_73:ThresholdAt 31 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 73 0 (by decide +kernel)
  | exact S 31 73 1 (by decide +kernel)
  | exact S 31 73 2 (by decide +kernel)
  | exact S 31 73 3 (by decide +kernel)
  | exact S 31 73 4 (by decide +kernel)
  | exact S 31 73 5 (by decide +kernel)
theorem q31_74:ThresholdAt 31 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 74 0 (by decide +kernel)
  | exact S 31 74 1 (by decide +kernel)
  | exact S 31 74 2 (by decide +kernel)
  | exact S 31 74 3 (by decide +kernel)
  | exact S 31 74 4 (by decide +kernel)
  | exact S 31 74 5 (by decide +kernel)
theorem q31_75:ThresholdAt 31 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 75 0 (by decide +kernel)
  | exact S 31 75 1 (by decide +kernel)
  | exact S 31 75 2 (by decide +kernel)
  | exact S 31 75 3 (by decide +kernel)
  | exact S 31 75 4 (by decide +kernel)
  | exact S 31 75 5 (by decide +kernel)
theorem q31_76:ThresholdAt 31 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 76 0 (by decide +kernel)
  | exact S 31 76 1 (by decide +kernel)
  | exact S 31 76 2 (by decide +kernel)
  | exact S 31 76 3 (by decide +kernel)
  | exact S 31 76 4 (by decide +kernel)
  | exact S 31 76 5 (by decide +kernel)
theorem q31_77:ThresholdAt 31 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 77 0 (by decide +kernel)
  | exact S 31 77 1 (by decide +kernel)
  | exact S 31 77 2 (by decide +kernel)
  | exact S 31 77 3 (by decide +kernel)
  | exact S 31 77 4 (by decide +kernel)
  | exact S 31 77 5 (by decide +kernel)
theorem q31_78:ThresholdAt 31 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 78 0 (by decide +kernel)
  | exact S 31 78 1 (by decide +kernel)
  | exact S 31 78 2 (by decide +kernel)
  | exact S 31 78 3 (by decide +kernel)
  | exact S 31 78 4 (by decide +kernel)
  | exact S 31 78 5 (by decide +kernel)
theorem q31_79:ThresholdAt 31 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 79 0 (by decide +kernel)
  | exact S 31 79 1 (by decide +kernel)
  | exact S 31 79 2 (by decide +kernel)
  | exact S 31 79 3 (by decide +kernel)
  | exact S 31 79 4 (by decide +kernel)
  | exact S 31 79 5 (by decide +kernel)
theorem q31_80:ThresholdAt 31 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 80 0 (by decide +kernel)
  | exact S 31 80 1 (by decide +kernel)
  | exact S 31 80 2 (by decide +kernel)
  | exact S 31 80 3 (by decide +kernel)
  | exact S 31 80 4 (by decide +kernel)
  | exact S 31 80 5 (by decide +kernel)
theorem q31_81:ThresholdAt 31 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 81 0 (by decide +kernel)
  | exact S 31 81 1 (by decide +kernel)
  | exact S 31 81 2 (by decide +kernel)
  | exact S 31 81 3 (by decide +kernel)
  | exact S 31 81 4 (by decide +kernel)
  | exact S 31 81 5 (by decide +kernel)
theorem q31_82:ThresholdAt 31 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 82 0 (by decide +kernel)
  | exact S 31 82 1 (by decide +kernel)
  | exact S 31 82 2 (by decide +kernel)
  | exact S 31 82 3 (by decide +kernel)
  | exact S 31 82 4 (by decide +kernel)
  | exact S 31 82 5 (by decide +kernel)
theorem q31_83:ThresholdAt 31 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 83 0 (by decide +kernel)
  | exact S 31 83 1 (by decide +kernel)
  | exact S 31 83 2 (by decide +kernel)
  | exact S 31 83 3 (by decide +kernel)
  | exact S 31 83 4 (by decide +kernel)
  | exact S 31 83 5 (by decide +kernel)
theorem q31_84:ThresholdAt 31 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 84 0 (by decide +kernel)
  | exact S 31 84 1 (by decide +kernel)
  | exact S 31 84 2 (by decide +kernel)
  | exact S 31 84 3 (by decide +kernel)
  | exact S 31 84 4 (by decide +kernel)
  | exact S 31 84 5 (by decide +kernel)
theorem q31_85:ThresholdAt 31 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 85 0 (by decide +kernel)
  | exact S 31 85 1 (by decide +kernel)
  | exact S 31 85 2 (by decide +kernel)
  | exact S 31 85 3 (by decide +kernel)
  | exact S 31 85 4 (by decide +kernel)
  | exact S 31 85 5 (by decide +kernel)
theorem q31_86:ThresholdAt 31 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 86 0 (by decide +kernel)
  | exact S 31 86 1 (by decide +kernel)
  | exact S 31 86 2 (by decide +kernel)
  | exact S 31 86 3 (by decide +kernel)
  | exact S 31 86 4 (by decide +kernel)
  | exact S 31 86 5 (by decide +kernel)
theorem q31_87:ThresholdAt 31 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 87 0 (by decide +kernel)
  | exact S 31 87 1 (by decide +kernel)
  | exact S 31 87 2 (by decide +kernel)
  | exact S 31 87 3 (by decide +kernel)
  | exact S 31 87 4 (by decide +kernel)
  | exact S 31 87 5 (by decide +kernel)
theorem q31_88:ThresholdAt 31 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 88 0 (by decide +kernel)
  | exact S 31 88 1 (by decide +kernel)
  | exact S 31 88 2 (by decide +kernel)
  | exact S 31 88 3 (by decide +kernel)
  | exact S 31 88 4 (by decide +kernel)
  | exact S 31 88 5 (by decide +kernel)
theorem q31_89:ThresholdAt 31 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 89 0 (by decide +kernel)
  | exact S 31 89 1 (by decide +kernel)
  | exact S 31 89 2 (by decide +kernel)
  | exact S 31 89 3 (by decide +kernel)
  | exact S 31 89 4 (by decide +kernel)
  | exact S 31 89 5 (by decide +kernel)
theorem q31_90:ThresholdAt 31 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 90 0 (by decide +kernel)
  | exact S 31 90 1 (by decide +kernel)
  | exact S 31 90 2 (by decide +kernel)
  | exact S 31 90 3 (by decide +kernel)
  | exact S 31 90 4 (by decide +kernel)
  | exact S 31 90 5 (by decide +kernel)
theorem q31_91:ThresholdAt 31 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 91 0 (by decide +kernel)
  | exact S 31 91 1 (by decide +kernel)
  | exact S 31 91 2 (by decide +kernel)
  | exact S 31 91 3 (by decide +kernel)
  | exact S 31 91 4 (by decide +kernel)
  | exact S 31 91 5 (by decide +kernel)
theorem q31_92:ThresholdAt 31 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 92 0 (by decide +kernel)
  | exact S 31 92 1 (by decide +kernel)
  | exact S 31 92 2 (by decide +kernel)
  | exact S 31 92 3 (by decide +kernel)
  | exact S 31 92 4 (by decide +kernel)
  | exact S 31 92 5 (by decide +kernel)
theorem q31_93:ThresholdAt 31 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 93 0 (by decide +kernel)
  | exact S 31 93 1 (by decide +kernel)
  | exact S 31 93 2 (by decide +kernel)
  | exact S 31 93 3 (by decide +kernel)
  | exact S 31 93 4 (by decide +kernel)
  | exact S 31 93 5 (by decide +kernel)
theorem q31_94:ThresholdAt 31 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 94 0 (by decide +kernel)
  | exact S 31 94 1 (by decide +kernel)
  | exact S 31 94 2 (by decide +kernel)
  | exact S 31 94 3 (by decide +kernel)
  | exact S 31 94 4 (by decide +kernel)
  | exact S 31 94 5 (by decide +kernel)
theorem q31_95:ThresholdAt 31 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 95 0 (by decide +kernel)
  | exact S 31 95 1 (by decide +kernel)
  | exact S 31 95 2 (by decide +kernel)
  | exact S 31 95 3 (by decide +kernel)
  | exact S 31 95 4 (by decide +kernel)
  | exact S 31 95 5 (by decide +kernel)
theorem q31_96:ThresholdAt 31 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 96 0 (by decide +kernel)
  | exact S 31 96 1 (by decide +kernel)
  | exact S 31 96 2 (by decide +kernel)
  | exact S 31 96 3 (by decide +kernel)
  | exact S 31 96 4 (by decide +kernel)
  | exact S 31 96 5 (by decide +kernel)
theorem q31_97:ThresholdAt 31 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 97 0 (by decide +kernel)
  | exact S 31 97 1 (by decide +kernel)
  | exact S 31 97 2 (by decide +kernel)
  | exact S 31 97 3 (by decide +kernel)
  | exact S 31 97 4 (by decide +kernel)
  | exact S 31 97 5 (by decide +kernel)
theorem q31_98:ThresholdAt 31 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 98 0 (by decide +kernel)
  | exact S 31 98 1 (by decide +kernel)
  | exact S 31 98 2 (by decide +kernel)
  | exact S 31 98 3 (by decide +kernel)
  | exact S 31 98 4 (by decide +kernel)
  | exact S 31 98 5 (by decide +kernel)
theorem q31_99:ThresholdAt 31 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 99 0 (by decide +kernel)
  | exact S 31 99 1 (by decide +kernel)
  | exact S 31 99 2 (by decide +kernel)
  | exact S 31 99 3 (by decide +kernel)
  | exact S 31 99 4 (by decide +kernel)
  | exact S 31 99 5 (by decide +kernel)
theorem q31_100:ThresholdAt 31 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 100 0 (by decide +kernel)
  | exact S 31 100 1 (by decide +kernel)
  | exact S 31 100 2 (by decide +kernel)
  | exact S 31 100 3 (by decide +kernel)
  | exact S 31 100 4 (by decide +kernel)
  | exact S 31 100 5 (by decide +kernel)
theorem q31_101:ThresholdAt 31 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 101 0 (by decide +kernel)
  | exact S 31 101 1 (by decide +kernel)
  | exact S 31 101 2 (by decide +kernel)
  | exact S 31 101 3 (by decide +kernel)
  | exact S 31 101 4 (by decide +kernel)
  | exact S 31 101 5 (by decide +kernel)
theorem q31_102:ThresholdAt 31 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 102 0 (by decide +kernel)
  | exact S 31 102 1 (by decide +kernel)
  | exact S 31 102 2 (by decide +kernel)
  | exact S 31 102 3 (by decide +kernel)
  | exact S 31 102 4 (by decide +kernel)
  | exact S 31 102 5 (by decide +kernel)
theorem q31_103:ThresholdAt 31 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 103 0 (by decide +kernel)
  | exact S 31 103 1 (by decide +kernel)
  | exact S 31 103 2 (by decide +kernel)
  | exact S 31 103 3 (by decide +kernel)
  | exact S 31 103 4 (by decide +kernel)
  | exact S 31 103 5 (by decide +kernel)
theorem q31_104:ThresholdAt 31 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 104 0 (by decide +kernel)
  | exact S 31 104 1 (by decide +kernel)
  | exact S 31 104 2 (by decide +kernel)
  | exact S 31 104 3 (by decide +kernel)
  | exact S 31 104 4 (by decide +kernel)
  | exact S 31 104 5 (by decide +kernel)
theorem q31_105:ThresholdAt 31 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 105 0 (by decide +kernel)
  | exact S 31 105 1 (by decide +kernel)
  | exact S 31 105 2 (by decide +kernel)
  | exact S 31 105 3 (by decide +kernel)
  | exact S 31 105 4 (by decide +kernel)
  | exact S 31 105 5 (by decide +kernel)
theorem q31_106:ThresholdAt 31 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 106 0 (by decide +kernel)
  | exact S 31 106 1 (by decide +kernel)
  | exact S 31 106 2 (by decide +kernel)
  | exact S 31 106 3 (by decide +kernel)
  | exact S 31 106 4 (by decide +kernel)
  | exact S 31 106 5 (by decide +kernel)
theorem q31_107:ThresholdAt 31 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 107 0 (by decide +kernel)
  | exact S 31 107 1 (by decide +kernel)
  | exact S 31 107 2 (by decide +kernel)
  | exact S 31 107 3 (by decide +kernel)
  | exact S 31 107 4 (by decide +kernel)
  | exact S 31 107 5 (by decide +kernel)
theorem q31_108:ThresholdAt 31 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 108 0 (by decide +kernel)
  | exact S 31 108 1 (by decide +kernel)
  | exact S 31 108 2 (by decide +kernel)
  | exact S 31 108 3 (by decide +kernel)
  | exact S 31 108 4 (by decide +kernel)
  | exact S 31 108 5 (by decide +kernel)
theorem q31_109:ThresholdAt 31 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 109 0 (by decide +kernel)
  | exact S 31 109 1 (by decide +kernel)
  | exact S 31 109 2 (by decide +kernel)
  | exact S 31 109 3 (by decide +kernel)
  | exact S 31 109 4 (by decide +kernel)
  | exact S 31 109 5 (by decide +kernel)
theorem q31_110:ThresholdAt 31 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 110 0 (by decide +kernel)
  | exact S 31 110 1 (by decide +kernel)
  | exact S 31 110 2 (by decide +kernel)
  | exact S 31 110 3 (by decide +kernel)
  | exact S 31 110 4 (by decide +kernel)
  | exact S 31 110 5 (by decide +kernel)
theorem q31_111:ThresholdAt 31 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 31 111 0 (by decide +kernel)
  | exact S 31 111 1 (by decide +kernel)
  | exact S 31 111 2 (by decide +kernel)
  | exact S 31 111 3 (by decide +kernel)
  | exact S 31 111 4 (by decide +kernel)
  | exact S 31 111 5 (by decide +kernel)
theorem checkedR31:∀ V ∈ List.range 112,ThresholdAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0_112:V < 56
  · by_cases h0_56:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q31_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q31_1
              · have he:V = 2:=by omega
                subst V
                exact q31_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q31_3
              · have he:V = 4:=by omega
                subst V
                exact q31_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q31_5
              · have he:V = 6:=by omega
                subst V
                exact q31_6
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have he:V = 7:=by omega
              subst V
              exact q31_7
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q31_8
              · have he:V = 9:=by omega
                subst V
                exact q31_9
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q31_10
              · have he:V = 11:=by omega
                subst V
                exact q31_11
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q31_12
              · have he:V = 13:=by omega
                subst V
                exact q31_13
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have he:V = 14:=by omega
              subst V
              exact q31_14
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q31_15
              · have he:V = 16:=by omega
                subst V
                exact q31_16
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q31_17
              · have he:V = 18:=by omega
                subst V
                exact q31_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q31_19
              · have he:V = 20:=by omega
                subst V
                exact q31_20
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have he:V = 21:=by omega
              subst V
              exact q31_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q31_22
              · have he:V = 23:=by omega
                subst V
                exact q31_23
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q31_24
              · have he:V = 25:=by omega
                subst V
                exact q31_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q31_26
              · have he:V = 27:=by omega
                subst V
                exact q31_27
    · by_cases h28_56:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have he:V = 28:=by omega
              subst V
              exact q31_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q31_29
              · have he:V = 30:=by omega
                subst V
                exact q31_30
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q31_31
              · have he:V = 32:=by omega
                subst V
                exact q31_32
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q31_33
              · have he:V = 34:=by omega
                subst V
                exact q31_34
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have he:V = 35:=by omega
              subst V
              exact q31_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q31_36
              · have he:V = 37:=by omega
                subst V
                exact q31_37
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q31_38
              · have he:V = 39:=by omega
                subst V
                exact q31_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q31_40
              · have he:V = 41:=by omega
                subst V
                exact q31_41
      · by_cases h42_56:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have he:V = 42:=by omega
              subst V
              exact q31_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q31_43
              · have he:V = 44:=by omega
                subst V
                exact q31_44
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q31_45
              · have he:V = 46:=by omega
                subst V
                exact q31_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q31_47
              · have he:V = 48:=by omega
                subst V
                exact q31_48
        · by_cases h49_56:V < 52
          · by_cases h49_52:V < 50
            · have he:V = 49:=by omega
              subst V
              exact q31_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q31_50
              · have he:V = 51:=by omega
                subst V
                exact q31_51
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q31_52
              · have he:V = 53:=by omega
                subst V
                exact q31_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q31_54
              · have he:V = 55:=by omega
                subst V
                exact q31_55
  · by_cases h56_112:V < 84
    · by_cases h56_84:V < 70
      · by_cases h56_70:V < 63
        · by_cases h56_63:V < 59
          · by_cases h56_59:V < 57
            · have he:V = 56:=by omega
              subst V
              exact q31_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q31_57
              · have he:V = 58:=by omega
                subst V
                exact q31_58
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q31_59
              · have he:V = 60:=by omega
                subst V
                exact q31_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q31_61
              · have he:V = 62:=by omega
                subst V
                exact q31_62
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have he:V = 63:=by omega
              subst V
              exact q31_63
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q31_64
              · have he:V = 65:=by omega
                subst V
                exact q31_65
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q31_66
              · have he:V = 67:=by omega
                subst V
                exact q31_67
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q31_68
              · have he:V = 69:=by omega
                subst V
                exact q31_69
      · by_cases h70_84:V < 77
        · by_cases h70_77:V < 73
          · by_cases h70_73:V < 71
            · have he:V = 70:=by omega
              subst V
              exact q31_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q31_71
              · have he:V = 72:=by omega
                subst V
                exact q31_72
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q31_73
              · have he:V = 74:=by omega
                subst V
                exact q31_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q31_75
              · have he:V = 76:=by omega
                subst V
                exact q31_76
        · by_cases h77_84:V < 80
          · by_cases h77_80:V < 78
            · have he:V = 77:=by omega
              subst V
              exact q31_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q31_78
              · have he:V = 79:=by omega
                subst V
                exact q31_79
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q31_80
              · have he:V = 81:=by omega
                subst V
                exact q31_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q31_82
              · have he:V = 83:=by omega
                subst V
                exact q31_83
    · by_cases h84_112:V < 98
      · by_cases h84_98:V < 91
        · by_cases h84_91:V < 87
          · by_cases h84_87:V < 85
            · have he:V = 84:=by omega
              subst V
              exact q31_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q31_85
              · have he:V = 86:=by omega
                subst V
                exact q31_86
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q31_87
              · have he:V = 88:=by omega
                subst V
                exact q31_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q31_89
              · have he:V = 90:=by omega
                subst V
                exact q31_90
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have he:V = 91:=by omega
              subst V
              exact q31_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q31_92
              · have he:V = 93:=by omega
                subst V
                exact q31_93
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q31_94
              · have he:V = 95:=by omega
                subst V
                exact q31_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q31_96
              · have he:V = 97:=by omega
                subst V
                exact q31_97
      · by_cases h98_112:V < 105
        · by_cases h98_105:V < 101
          · by_cases h98_101:V < 99
            · have he:V = 98:=by omega
              subst V
              exact q31_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q31_99
              · have he:V = 100:=by omega
                subst V
                exact q31_100
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q31_101
              · have he:V = 102:=by omega
                subst V
                exact q31_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q31_103
              · have he:V = 104:=by omega
                subst V
                exact q31_104
        · by_cases h105_112:V < 108
          · by_cases h105_108:V < 106
            · have he:V = 105:=by omega
              subst V
              exact q31_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q31_106
              · have he:V = 107:=by omega
                subst V
                exact q31_107
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q31_108
              · have he:V = 109:=by omega
                subst V
                exact q31_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q31_110
              · have he:V = 111:=by omega
                subst V
                exact q31_111
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
