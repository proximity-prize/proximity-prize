import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked09

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q10_0:ThresholdAt 10 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 0 0 (by decide +kernel)
  | exact S 10 0 1 (by decide +kernel)
  | exact S 10 0 2 (by decide +kernel)
  | exact S 10 0 3 (by decide +kernel)
  | exact S 10 0 4 (by decide +kernel)
  | exact S 10 0 5 (by decide +kernel)
theorem q10_1:ThresholdAt 10 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 1 0 (by decide +kernel)
  | exact S 10 1 1 (by decide +kernel)
  | exact S 10 1 2 (by decide +kernel)
  | exact S 10 1 3 (by decide +kernel)
  | exact S 10 1 4 (by decide +kernel)
  | exact S 10 1 5 (by decide +kernel)
theorem q10_2:ThresholdAt 10 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 2 0 (by decide +kernel)
  | exact S 10 2 1 (by decide +kernel)
  | exact S 10 2 2 (by decide +kernel)
  | exact S 10 2 3 (by decide +kernel)
  | exact S 10 2 4 (by decide +kernel)
  | exact S 10 2 5 (by decide +kernel)
theorem q10_3:ThresholdAt 10 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 3 0 (by decide +kernel)
  | exact S 10 3 1 (by decide +kernel)
  | exact S 10 3 2 (by decide +kernel)
  | exact S 10 3 3 (by decide +kernel)
  | exact S 10 3 4 (by decide +kernel)
  | exact S 10 3 5 (by decide +kernel)
theorem q10_4:ThresholdAt 10 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 4 0 (by decide +kernel)
  | exact S 10 4 1 (by decide +kernel)
  | exact S 10 4 2 (by decide +kernel)
  | exact S 10 4 3 (by decide +kernel)
  | exact S 10 4 4 (by decide +kernel)
  | exact S 10 4 5 (by decide +kernel)
theorem q10_5:ThresholdAt 10 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 5 0 (by decide +kernel)
  | exact S 10 5 1 (by decide +kernel)
  | exact S 10 5 2 (by decide +kernel)
  | exact S 10 5 3 (by decide +kernel)
  | exact S 10 5 4 (by decide +kernel)
  | exact S 10 5 5 (by decide +kernel)
theorem q10_6:ThresholdAt 10 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 6 0 (by decide +kernel)
  | exact S 10 6 1 (by decide +kernel)
  | exact S 10 6 2 (by decide +kernel)
  | exact S 10 6 3 (by decide +kernel)
  | exact S 10 6 4 (by decide +kernel)
  | exact S 10 6 5 (by decide +kernel)
theorem q10_7:ThresholdAt 10 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 7 0 (by decide +kernel)
  | exact S 10 7 1 (by decide +kernel)
  | exact S 10 7 2 (by decide +kernel)
  | exact S 10 7 3 (by decide +kernel)
  | exact S 10 7 4 (by decide +kernel)
  | exact S 10 7 5 (by decide +kernel)
theorem q10_8:ThresholdAt 10 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 8 0 (by decide +kernel)
  | exact S 10 8 1 (by decide +kernel)
  | exact S 10 8 2 (by decide +kernel)
  | exact S 10 8 3 (by decide +kernel)
  | exact S 10 8 4 (by decide +kernel)
  | exact S 10 8 5 (by decide +kernel)
theorem q10_9:ThresholdAt 10 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 9 0 (by decide +kernel)
  | exact S 10 9 1 (by decide +kernel)
  | exact S 10 9 2 (by decide +kernel)
  | exact S 10 9 3 (by decide +kernel)
  | exact S 10 9 4 (by decide +kernel)
  | exact S 10 9 5 (by decide +kernel)
theorem q10_10:ThresholdAt 10 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 10 0 (by decide +kernel)
  | exact S 10 10 1 (by decide +kernel)
  | exact S 10 10 2 (by decide +kernel)
  | exact S 10 10 3 (by decide +kernel)
  | exact S 10 10 4 (by decide +kernel)
  | exact S 10 10 5 (by decide +kernel)
theorem q10_11:ThresholdAt 10 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 11 0 (by decide +kernel)
  | exact S 10 11 1 (by decide +kernel)
  | exact S 10 11 2 (by decide +kernel)
  | exact S 10 11 3 (by decide +kernel)
  | exact S 10 11 4 (by decide +kernel)
  | exact S 10 11 5 (by decide +kernel)
theorem q10_12:ThresholdAt 10 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 12 0 (by decide +kernel)
  | exact S 10 12 1 (by decide +kernel)
  | exact S 10 12 2 (by decide +kernel)
  | exact S 10 12 3 (by decide +kernel)
  | exact S 10 12 4 (by decide +kernel)
  | exact S 10 12 5 (by decide +kernel)
theorem q10_13:ThresholdAt 10 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 13 0 (by decide +kernel)
  | exact S 10 13 1 (by decide +kernel)
  | exact S 10 13 2 (by decide +kernel)
  | exact S 10 13 3 (by decide +kernel)
  | exact S 10 13 4 (by decide +kernel)
  | exact S 10 13 5 (by decide +kernel)
theorem q10_14:ThresholdAt 10 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 14 0 (by decide +kernel)
  | exact S 10 14 1 (by decide +kernel)
  | exact S 10 14 2 (by decide +kernel)
  | exact S 10 14 3 (by decide +kernel)
  | exact S 10 14 4 (by decide +kernel)
  | exact S 10 14 5 (by decide +kernel)
theorem q10_15:ThresholdAt 10 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 15 0 (by decide +kernel)
  | exact S 10 15 1 (by decide +kernel)
  | exact S 10 15 2 (by decide +kernel)
  | exact S 10 15 3 (by decide +kernel)
  | exact S 10 15 4 (by decide +kernel)
  | exact S 10 15 5 (by decide +kernel)
theorem q10_16:ThresholdAt 10 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 16 0 (by decide +kernel)
  | exact S 10 16 1 (by decide +kernel)
  | exact S 10 16 2 (by decide +kernel)
  | exact S 10 16 3 (by decide +kernel)
  | exact S 10 16 4 (by decide +kernel)
  | exact S 10 16 5 (by decide +kernel)
theorem q10_17:ThresholdAt 10 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 17 0 (by decide +kernel)
  | exact S 10 17 1 (by decide +kernel)
  | exact S 10 17 2 (by decide +kernel)
  | exact S 10 17 3 (by decide +kernel)
  | exact S 10 17 4 (by decide +kernel)
  | exact S 10 17 5 (by decide +kernel)
theorem q10_18:ThresholdAt 10 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 18 0 (by decide +kernel)
  | exact S 10 18 1 (by decide +kernel)
  | exact S 10 18 2 (by decide +kernel)
  | exact S 10 18 3 (by decide +kernel)
  | exact S 10 18 4 (by decide +kernel)
  | exact S 10 18 5 (by decide +kernel)
theorem q10_19:ThresholdAt 10 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 19 0 (by decide +kernel)
  | exact S 10 19 1 (by decide +kernel)
  | exact S 10 19 2 (by decide +kernel)
  | exact S 10 19 3 (by decide +kernel)
  | exact S 10 19 4 (by decide +kernel)
  | exact S 10 19 5 (by decide +kernel)
theorem q10_20:ThresholdAt 10 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 20 0 (by decide +kernel)
  | exact S 10 20 1 (by decide +kernel)
  | exact S 10 20 2 (by decide +kernel)
  | exact S 10 20 3 (by decide +kernel)
  | exact S 10 20 4 (by decide +kernel)
  | exact S 10 20 5 (by decide +kernel)
theorem q10_21:ThresholdAt 10 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 21 0 (by decide +kernel)
  | exact S 10 21 1 (by decide +kernel)
  | exact S 10 21 2 (by decide +kernel)
  | exact S 10 21 3 (by decide +kernel)
  | exact S 10 21 4 (by decide +kernel)
  | exact S 10 21 5 (by decide +kernel)
theorem q10_22:ThresholdAt 10 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 22 0 (by decide +kernel)
  | exact S 10 22 1 (by decide +kernel)
  | exact S 10 22 2 (by decide +kernel)
  | exact S 10 22 3 (by decide +kernel)
  | exact S 10 22 4 (by decide +kernel)
  | exact S 10 22 5 (by decide +kernel)
theorem q10_23:ThresholdAt 10 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 23 0 (by decide +kernel)
  | exact S 10 23 1 (by decide +kernel)
  | exact S 10 23 2 (by decide +kernel)
  | exact S 10 23 3 (by decide +kernel)
  | exact S 10 23 4 (by decide +kernel)
  | exact S 10 23 5 (by decide +kernel)
theorem q10_24:ThresholdAt 10 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 24 0 (by decide +kernel)
  | exact S 10 24 1 (by decide +kernel)
  | exact S 10 24 2 (by decide +kernel)
  | exact S 10 24 3 (by decide +kernel)
  | exact S 10 24 4 (by decide +kernel)
  | exact S 10 24 5 (by decide +kernel)
theorem q10_25:ThresholdAt 10 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 25 0 (by decide +kernel)
  | exact S 10 25 1 (by decide +kernel)
  | exact S 10 25 2 (by decide +kernel)
  | exact S 10 25 3 (by decide +kernel)
  | exact S 10 25 4 (by decide +kernel)
  | exact S 10 25 5 (by decide +kernel)
theorem q10_26:ThresholdAt 10 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 26 0 (by decide +kernel)
  | exact S 10 26 1 (by decide +kernel)
  | exact S 10 26 2 (by decide +kernel)
  | exact S 10 26 3 (by decide +kernel)
  | exact S 10 26 4 (by decide +kernel)
  | exact S 10 26 5 (by decide +kernel)
theorem q10_27:ThresholdAt 10 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 27 0 (by decide +kernel)
  | exact S 10 27 1 (by decide +kernel)
  | exact S 10 27 2 (by decide +kernel)
  | exact S 10 27 3 (by decide +kernel)
  | exact S 10 27 4 (by decide +kernel)
  | exact S 10 27 5 (by decide +kernel)
theorem q10_28:ThresholdAt 10 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 28 0 (by decide +kernel)
  | exact S 10 28 1 (by decide +kernel)
  | exact S 10 28 2 (by decide +kernel)
  | exact S 10 28 3 (by decide +kernel)
  | exact S 10 28 4 (by decide +kernel)
  | exact S 10 28 5 (by decide +kernel)
theorem q10_29:ThresholdAt 10 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 29 0 (by decide +kernel)
  | exact S 10 29 1 (by decide +kernel)
  | exact S 10 29 2 (by decide +kernel)
  | exact S 10 29 3 (by decide +kernel)
  | exact S 10 29 4 (by decide +kernel)
  | exact S 10 29 5 (by decide +kernel)
theorem q10_30:ThresholdAt 10 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 30 0 (by decide +kernel)
  | exact S 10 30 1 (by decide +kernel)
  | exact S 10 30 2 (by decide +kernel)
  | exact S 10 30 3 (by decide +kernel)
  | exact S 10 30 4 (by decide +kernel)
  | exact S 10 30 5 (by decide +kernel)
theorem q10_31:ThresholdAt 10 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 31 0 (by decide +kernel)
  | exact S 10 31 1 (by decide +kernel)
  | exact S 10 31 2 (by decide +kernel)
  | exact S 10 31 3 (by decide +kernel)
  | exact S 10 31 4 (by decide +kernel)
  | exact S 10 31 5 (by decide +kernel)
theorem q10_32:ThresholdAt 10 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 32 0 (by decide +kernel)
  | exact S 10 32 1 (by decide +kernel)
  | exact S 10 32 2 (by decide +kernel)
  | exact S 10 32 3 (by decide +kernel)
  | exact S 10 32 4 (by decide +kernel)
  | exact S 10 32 5 (by decide +kernel)
theorem q10_33:ThresholdAt 10 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 33 0 (by decide +kernel)
  | exact S 10 33 1 (by decide +kernel)
  | exact S 10 33 2 (by decide +kernel)
  | exact S 10 33 3 (by decide +kernel)
  | exact S 10 33 4 (by decide +kernel)
  | exact S 10 33 5 (by decide +kernel)
theorem q10_34:ThresholdAt 10 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 34 0 (by decide +kernel)
  | exact S 10 34 1 (by decide +kernel)
  | exact S 10 34 2 (by decide +kernel)
  | exact S 10 34 3 (by decide +kernel)
  | exact S 10 34 4 (by decide +kernel)
  | exact S 10 34 5 (by decide +kernel)
theorem q10_35:ThresholdAt 10 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 35 0 (by decide +kernel)
  | exact S 10 35 1 (by decide +kernel)
  | exact S 10 35 2 (by decide +kernel)
  | exact S 10 35 3 (by decide +kernel)
  | exact S 10 35 4 (by decide +kernel)
  | exact S 10 35 5 (by decide +kernel)
theorem q10_36:ThresholdAt 10 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 36 0 (by decide +kernel)
  | exact S 10 36 1 (by decide +kernel)
  | exact S 10 36 2 (by decide +kernel)
  | exact S 10 36 3 (by decide +kernel)
  | exact S 10 36 4 (by decide +kernel)
  | exact S 10 36 5 (by decide +kernel)
theorem q10_37:ThresholdAt 10 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 37 0 (by decide +kernel)
  | exact S 10 37 1 (by decide +kernel)
  | exact S 10 37 2 (by decide +kernel)
  | exact S 10 37 3 (by decide +kernel)
  | exact S 10 37 4 (by decide +kernel)
  | exact S 10 37 5 (by decide +kernel)
theorem q10_38:ThresholdAt 10 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 38 0 (by decide +kernel)
  | exact S 10 38 1 (by decide +kernel)
  | exact S 10 38 2 (by decide +kernel)
  | exact S 10 38 3 (by decide +kernel)
  | exact S 10 38 4 (by decide +kernel)
  | exact S 10 38 5 (by decide +kernel)
theorem q10_39:ThresholdAt 10 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 39 0 (by decide +kernel)
  | exact S 10 39 1 (by decide +kernel)
  | exact S 10 39 2 (by decide +kernel)
  | exact S 10 39 3 (by decide +kernel)
  | exact S 10 39 4 (by decide +kernel)
  | exact S 10 39 5 (by decide +kernel)
theorem q10_40:ThresholdAt 10 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 40 0 (by decide +kernel)
  | exact S 10 40 1 (by decide +kernel)
  | exact S 10 40 2 (by decide +kernel)
  | exact S 10 40 3 (by decide +kernel)
  | exact S 10 40 4 (by decide +kernel)
  | exact S 10 40 5 (by decide +kernel)
theorem q10_41:ThresholdAt 10 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 41 0 (by decide +kernel)
  | exact S 10 41 1 (by decide +kernel)
  | exact S 10 41 2 (by decide +kernel)
  | exact S 10 41 3 (by decide +kernel)
  | exact S 10 41 4 (by decide +kernel)
  | exact S 10 41 5 (by decide +kernel)
theorem q10_42:ThresholdAt 10 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 42 0 (by decide +kernel)
  | exact S 10 42 1 (by decide +kernel)
  | exact S 10 42 2 (by decide +kernel)
  | exact S 10 42 3 (by decide +kernel)
  | exact S 10 42 4 (by decide +kernel)
  | exact S 10 42 5 (by decide +kernel)
theorem q10_43:ThresholdAt 10 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 43 0 (by decide +kernel)
  | exact S 10 43 1 (by decide +kernel)
  | exact S 10 43 2 (by decide +kernel)
  | exact S 10 43 3 (by decide +kernel)
  | exact S 10 43 4 (by decide +kernel)
  | exact S 10 43 5 (by decide +kernel)
theorem q10_44:ThresholdAt 10 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 44 0 (by decide +kernel)
  | exact S 10 44 1 (by decide +kernel)
  | exact S 10 44 2 (by decide +kernel)
  | exact S 10 44 3 (by decide +kernel)
  | exact S 10 44 4 (by decide +kernel)
  | exact S 10 44 5 (by decide +kernel)
theorem q10_45:ThresholdAt 10 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 45 0 (by decide +kernel)
  | exact S 10 45 1 (by decide +kernel)
  | exact S 10 45 2 (by decide +kernel)
  | exact S 10 45 3 (by decide +kernel)
  | exact S 10 45 4 (by decide +kernel)
  | exact S 10 45 5 (by decide +kernel)
theorem q10_46:ThresholdAt 10 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 46 0 (by decide +kernel)
  | exact S 10 46 1 (by decide +kernel)
  | exact S 10 46 2 (by decide +kernel)
  | exact S 10 46 3 (by decide +kernel)
  | exact S 10 46 4 (by decide +kernel)
  | exact S 10 46 5 (by decide +kernel)
theorem q10_47:ThresholdAt 10 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 47 0 (by decide +kernel)
  | exact S 10 47 1 (by decide +kernel)
  | exact S 10 47 2 (by decide +kernel)
  | exact S 10 47 3 (by decide +kernel)
  | exact S 10 47 4 (by decide +kernel)
  | exact S 10 47 5 (by decide +kernel)
theorem q10_48:ThresholdAt 10 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 48 0 (by decide +kernel)
  | exact S 10 48 1 (by decide +kernel)
  | exact S 10 48 2 (by decide +kernel)
  | exact S 10 48 3 (by decide +kernel)
  | exact S 10 48 4 (by decide +kernel)
  | exact S 10 48 5 (by decide +kernel)
theorem q10_49:ThresholdAt 10 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 49 0 (by decide +kernel)
  | exact S 10 49 1 (by decide +kernel)
  | exact S 10 49 2 (by decide +kernel)
  | exact S 10 49 3 (by decide +kernel)
  | exact S 10 49 4 (by decide +kernel)
  | exact S 10 49 5 (by decide +kernel)
theorem q10_50:ThresholdAt 10 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 50 0 (by decide +kernel)
  | exact S 10 50 1 (by decide +kernel)
  | exact S 10 50 2 (by decide +kernel)
  | exact S 10 50 3 (by decide +kernel)
  | exact S 10 50 4 (by decide +kernel)
  | exact S 10 50 5 (by decide +kernel)
theorem q10_51:ThresholdAt 10 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 51 0 (by decide +kernel)
  | exact S 10 51 1 (by decide +kernel)
  | exact S 10 51 2 (by decide +kernel)
  | exact S 10 51 3 (by decide +kernel)
  | exact S 10 51 4 (by decide +kernel)
  | exact S 10 51 5 (by decide +kernel)
theorem q10_52:ThresholdAt 10 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 52 0 (by decide +kernel)
  | exact S 10 52 1 (by decide +kernel)
  | exact S 10 52 2 (by decide +kernel)
  | exact S 10 52 3 (by decide +kernel)
  | exact S 10 52 4 (by decide +kernel)
  | exact S 10 52 5 (by decide +kernel)
theorem q10_53:ThresholdAt 10 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 53 0 (by decide +kernel)
  | exact S 10 53 1 (by decide +kernel)
  | exact S 10 53 2 (by decide +kernel)
  | exact S 10 53 3 (by decide +kernel)
  | exact S 10 53 4 (by decide +kernel)
  | exact S 10 53 5 (by decide +kernel)
theorem q10_54:ThresholdAt 10 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 54 0 (by decide +kernel)
  | exact S 10 54 1 (by decide +kernel)
  | exact S 10 54 2 (by decide +kernel)
  | exact S 10 54 3 (by decide +kernel)
  | exact S 10 54 4 (by decide +kernel)
  | exact S 10 54 5 (by decide +kernel)
theorem q10_55:ThresholdAt 10 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 55 0 (by decide +kernel)
  | exact S 10 55 1 (by decide +kernel)
  | exact S 10 55 2 (by decide +kernel)
  | exact S 10 55 3 (by decide +kernel)
  | exact S 10 55 4 (by decide +kernel)
  | exact S 10 55 5 (by decide +kernel)
theorem q10_56:ThresholdAt 10 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 56 0 (by decide +kernel)
  | exact S 10 56 1 (by decide +kernel)
  | exact S 10 56 2 (by decide +kernel)
  | exact S 10 56 3 (by decide +kernel)
  | exact S 10 56 4 (by decide +kernel)
  | exact S 10 56 5 (by decide +kernel)
theorem q10_57:ThresholdAt 10 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 57 0 (by decide +kernel)
  | exact S 10 57 1 (by decide +kernel)
  | exact S 10 57 2 (by decide +kernel)
  | exact S 10 57 3 (by decide +kernel)
  | exact S 10 57 4 (by decide +kernel)
  | exact S 10 57 5 (by decide +kernel)
theorem q10_58:ThresholdAt 10 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 58 0 (by decide +kernel)
  | exact S 10 58 1 (by decide +kernel)
  | exact S 10 58 2 (by decide +kernel)
  | exact S 10 58 3 (by decide +kernel)
  | exact S 10 58 4 (by decide +kernel)
  | exact S 10 58 5 (by decide +kernel)
theorem q10_59:ThresholdAt 10 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 59 0 (by decide +kernel)
  | exact S 10 59 1 (by decide +kernel)
  | exact S 10 59 2 (by decide +kernel)
  | exact S 10 59 3 (by decide +kernel)
  | exact S 10 59 4 (by decide +kernel)
  | exact S 10 59 5 (by decide +kernel)
theorem q10_60:ThresholdAt 10 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 60 0 (by decide +kernel)
  | exact S 10 60 1 (by decide +kernel)
  | exact S 10 60 2 (by decide +kernel)
  | exact S 10 60 3 (by decide +kernel)
  | exact S 10 60 4 (by decide +kernel)
  | exact S 10 60 5 (by decide +kernel)
theorem q10_61:ThresholdAt 10 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 61 0 (by decide +kernel)
  | exact S 10 61 1 (by decide +kernel)
  | exact S 10 61 2 (by decide +kernel)
  | exact S 10 61 3 (by decide +kernel)
  | exact S 10 61 4 (by decide +kernel)
  | exact S 10 61 5 (by decide +kernel)
theorem q10_62:ThresholdAt 10 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 62 0 (by decide +kernel)
  | exact S 10 62 1 (by decide +kernel)
  | exact S 10 62 2 (by decide +kernel)
  | exact S 10 62 3 (by decide +kernel)
  | exact S 10 62 4 (by decide +kernel)
  | exact S 10 62 5 (by decide +kernel)
theorem q10_63:ThresholdAt 10 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 63 0 (by decide +kernel)
  | exact S 10 63 1 (by decide +kernel)
  | exact S 10 63 2 (by decide +kernel)
  | exact S 10 63 3 (by decide +kernel)
  | exact S 10 63 4 (by decide +kernel)
  | exact S 10 63 5 (by decide +kernel)
theorem q10_64:ThresholdAt 10 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 64 0 (by decide +kernel)
  | exact S 10 64 1 (by decide +kernel)
  | exact S 10 64 2 (by decide +kernel)
  | exact S 10 64 3 (by decide +kernel)
  | exact S 10 64 4 (by decide +kernel)
  | exact S 10 64 5 (by decide +kernel)
theorem q10_65:ThresholdAt 10 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 65 0 (by decide +kernel)
  | exact S 10 65 1 (by decide +kernel)
  | exact S 10 65 2 (by decide +kernel)
  | exact S 10 65 3 (by decide +kernel)
  | exact S 10 65 4 (by decide +kernel)
  | exact S 10 65 5 (by decide +kernel)
theorem q10_66:ThresholdAt 10 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 66 0 (by decide +kernel)
  | exact S 10 66 1 (by decide +kernel)
  | exact S 10 66 2 (by decide +kernel)
  | exact S 10 66 3 (by decide +kernel)
  | exact S 10 66 4 (by decide +kernel)
  | exact S 10 66 5 (by decide +kernel)
theorem q10_67:ThresholdAt 10 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 67 0 (by decide +kernel)
  | exact S 10 67 1 (by decide +kernel)
  | exact S 10 67 2 (by decide +kernel)
  | exact S 10 67 3 (by decide +kernel)
  | exact S 10 67 4 (by decide +kernel)
  | exact S 10 67 5 (by decide +kernel)
theorem q10_68:ThresholdAt 10 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 68 0 (by decide +kernel)
  | exact S 10 68 1 (by decide +kernel)
  | exact S 10 68 2 (by decide +kernel)
  | exact S 10 68 3 (by decide +kernel)
  | exact S 10 68 4 (by decide +kernel)
  | exact S 10 68 5 (by decide +kernel)
theorem q10_69:ThresholdAt 10 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 69 0 (by decide +kernel)
  | exact S 10 69 1 (by decide +kernel)
  | exact S 10 69 2 (by decide +kernel)
  | exact S 10 69 3 (by decide +kernel)
  | exact S 10 69 4 (by decide +kernel)
  | exact S 10 69 5 (by decide +kernel)
theorem q10_70:ThresholdAt 10 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 70 0 (by decide +kernel)
  | exact S 10 70 1 (by decide +kernel)
  | exact S 10 70 2 (by decide +kernel)
  | exact S 10 70 3 (by decide +kernel)
  | exact S 10 70 4 (by decide +kernel)
  | exact S 10 70 5 (by decide +kernel)
theorem q10_71:ThresholdAt 10 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 71 0 (by decide +kernel)
  | exact S 10 71 1 (by decide +kernel)
  | exact S 10 71 2 (by decide +kernel)
  | exact S 10 71 3 (by decide +kernel)
  | exact S 10 71 4 (by decide +kernel)
  | exact S 10 71 5 (by decide +kernel)
theorem q10_72:ThresholdAt 10 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 72 0 (by decide +kernel)
  | exact S 10 72 1 (by decide +kernel)
  | exact S 10 72 2 (by decide +kernel)
  | exact S 10 72 3 (by decide +kernel)
  | exact S 10 72 4 (by decide +kernel)
  | exact S 10 72 5 (by decide +kernel)
theorem q10_73:ThresholdAt 10 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 73 0 (by decide +kernel)
  | exact S 10 73 1 (by decide +kernel)
  | exact S 10 73 2 (by decide +kernel)
  | exact S 10 73 3 (by decide +kernel)
  | exact S 10 73 4 (by decide +kernel)
  | exact S 10 73 5 (by decide +kernel)
theorem q10_74:ThresholdAt 10 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 74 0 (by decide +kernel)
  | exact S 10 74 1 (by decide +kernel)
  | exact S 10 74 2 (by decide +kernel)
  | exact S 10 74 3 (by decide +kernel)
  | exact S 10 74 4 (by decide +kernel)
  | exact S 10 74 5 (by decide +kernel)
theorem q10_75:ThresholdAt 10 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 75 0 (by decide +kernel)
  | exact S 10 75 1 (by decide +kernel)
  | exact S 10 75 2 (by decide +kernel)
  | exact S 10 75 3 (by decide +kernel)
  | exact S 10 75 4 (by decide +kernel)
  | exact S 10 75 5 (by decide +kernel)
theorem q10_76:ThresholdAt 10 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 76 0 (by decide +kernel)
  | exact S 10 76 1 (by decide +kernel)
  | exact S 10 76 2 (by decide +kernel)
  | exact S 10 76 3 (by decide +kernel)
  | exact S 10 76 4 (by decide +kernel)
  | exact S 10 76 5 (by decide +kernel)
theorem q10_77:ThresholdAt 10 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 77 0 (by decide +kernel)
  | exact S 10 77 1 (by decide +kernel)
  | exact S 10 77 2 (by decide +kernel)
  | exact S 10 77 3 (by decide +kernel)
  | exact S 10 77 4 (by decide +kernel)
  | exact S 10 77 5 (by decide +kernel)
theorem q10_78:ThresholdAt 10 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 78 0 (by decide +kernel)
  | exact S 10 78 1 (by decide +kernel)
  | exact S 10 78 2 (by decide +kernel)
  | exact S 10 78 3 (by decide +kernel)
  | exact S 10 78 4 (by decide +kernel)
  | exact S 10 78 5 (by decide +kernel)
theorem q10_79:ThresholdAt 10 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 79 0 (by decide +kernel)
  | exact S 10 79 1 (by decide +kernel)
  | exact S 10 79 2 (by decide +kernel)
  | exact S 10 79 3 (by decide +kernel)
  | exact S 10 79 4 (by decide +kernel)
  | exact S 10 79 5 (by decide +kernel)
theorem q10_80:ThresholdAt 10 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 80 0 (by decide +kernel)
  | exact S 10 80 1 (by decide +kernel)
  | exact S 10 80 2 (by decide +kernel)
  | exact S 10 80 3 (by decide +kernel)
  | exact S 10 80 4 (by decide +kernel)
  | exact S 10 80 5 (by decide +kernel)
theorem q10_81:ThresholdAt 10 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 81 0 (by decide +kernel)
  | exact S 10 81 1 (by decide +kernel)
  | exact S 10 81 2 (by decide +kernel)
  | exact S 10 81 3 (by decide +kernel)
  | exact S 10 81 4 (by decide +kernel)
  | exact S 10 81 5 (by decide +kernel)
theorem q10_82:ThresholdAt 10 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 82 0 (by decide +kernel)
  | exact S 10 82 1 (by decide +kernel)
  | exact S 10 82 2 (by decide +kernel)
  | exact S 10 82 3 (by decide +kernel)
  | exact S 10 82 4 (by decide +kernel)
  | exact S 10 82 5 (by decide +kernel)
theorem q10_83:ThresholdAt 10 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 83 0 (by decide +kernel)
  | exact S 10 83 1 (by decide +kernel)
  | exact S 10 83 2 (by decide +kernel)
  | exact S 10 83 3 (by decide +kernel)
  | exact S 10 83 4 (by decide +kernel)
  | exact S 10 83 5 (by decide +kernel)
theorem q10_84:ThresholdAt 10 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 84 0 (by decide +kernel)
  | exact S 10 84 1 (by decide +kernel)
  | exact S 10 84 2 (by decide +kernel)
  | exact S 10 84 3 (by decide +kernel)
  | exact S 10 84 4 (by decide +kernel)
  | exact S 10 84 5 (by decide +kernel)
theorem q10_85:ThresholdAt 10 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 85 0 (by decide +kernel)
  | exact S 10 85 1 (by decide +kernel)
  | exact S 10 85 2 (by decide +kernel)
  | exact S 10 85 3 (by decide +kernel)
  | exact S 10 85 4 (by decide +kernel)
  | exact S 10 85 5 (by decide +kernel)
theorem q10_86:ThresholdAt 10 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 86 0 (by decide +kernel)
  | exact S 10 86 1 (by decide +kernel)
  | exact S 10 86 2 (by decide +kernel)
  | exact S 10 86 3 (by decide +kernel)
  | exact S 10 86 4 (by decide +kernel)
  | exact S 10 86 5 (by decide +kernel)
theorem q10_87:ThresholdAt 10 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 87 0 (by decide +kernel)
  | exact S 10 87 1 (by decide +kernel)
  | exact S 10 87 2 (by decide +kernel)
  | exact S 10 87 3 (by decide +kernel)
  | exact S 10 87 4 (by decide +kernel)
  | exact S 10 87 5 (by decide +kernel)
theorem q10_88:ThresholdAt 10 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 88 0 (by decide +kernel)
  | exact S 10 88 1 (by decide +kernel)
  | exact S 10 88 2 (by decide +kernel)
  | exact S 10 88 3 (by decide +kernel)
  | exact S 10 88 4 (by decide +kernel)
  | exact S 10 88 5 (by decide +kernel)
theorem q10_89:ThresholdAt 10 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 89 0 (by decide +kernel)
  | exact S 10 89 1 (by decide +kernel)
  | exact S 10 89 2 (by decide +kernel)
  | exact S 10 89 3 (by decide +kernel)
  | exact S 10 89 4 (by decide +kernel)
  | exact S 10 89 5 (by decide +kernel)
theorem q10_90:ThresholdAt 10 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 90 0 (by decide +kernel)
  | exact S 10 90 1 (by decide +kernel)
  | exact S 10 90 2 (by decide +kernel)
  | exact S 10 90 3 (by decide +kernel)
  | exact S 10 90 4 (by decide +kernel)
  | exact S 10 90 5 (by decide +kernel)
theorem q10_91:ThresholdAt 10 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 91 0 (by decide +kernel)
  | exact S 10 91 1 (by decide +kernel)
  | exact S 10 91 2 (by decide +kernel)
  | exact S 10 91 3 (by decide +kernel)
  | exact S 10 91 4 (by decide +kernel)
  | exact S 10 91 5 (by decide +kernel)
theorem q10_92:ThresholdAt 10 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 92 0 (by decide +kernel)
  | exact S 10 92 1 (by decide +kernel)
  | exact S 10 92 2 (by decide +kernel)
  | exact S 10 92 3 (by decide +kernel)
  | exact S 10 92 4 (by decide +kernel)
  | exact S 10 92 5 (by decide +kernel)
theorem q10_93:ThresholdAt 10 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 93 0 (by decide +kernel)
  | exact S 10 93 1 (by decide +kernel)
  | exact S 10 93 2 (by decide +kernel)
  | exact S 10 93 3 (by decide +kernel)
  | exact S 10 93 4 (by decide +kernel)
  | exact S 10 93 5 (by decide +kernel)
theorem q10_94:ThresholdAt 10 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 94 0 (by decide +kernel)
  | exact S 10 94 1 (by decide +kernel)
  | exact S 10 94 2 (by decide +kernel)
  | exact S 10 94 3 (by decide +kernel)
  | exact S 10 94 4 (by decide +kernel)
  | exact S 10 94 5 (by decide +kernel)
theorem q10_95:ThresholdAt 10 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 95 0 (by decide +kernel)
  | exact S 10 95 1 (by decide +kernel)
  | exact S 10 95 2 (by decide +kernel)
  | exact S 10 95 3 (by decide +kernel)
  | exact S 10 95 4 (by decide +kernel)
  | exact S 10 95 5 (by decide +kernel)
theorem q10_96:ThresholdAt 10 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 96 0 (by decide +kernel)
  | exact S 10 96 1 (by decide +kernel)
  | exact S 10 96 2 (by decide +kernel)
  | exact S 10 96 3 (by decide +kernel)
  | exact S 10 96 4 (by decide +kernel)
  | exact S 10 96 5 (by decide +kernel)
theorem q10_97:ThresholdAt 10 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 97 0 (by decide +kernel)
  | exact S 10 97 1 (by decide +kernel)
  | exact S 10 97 2 (by decide +kernel)
  | exact S 10 97 3 (by decide +kernel)
  | exact S 10 97 4 (by decide +kernel)
  | exact S 10 97 5 (by decide +kernel)
theorem q10_98:ThresholdAt 10 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 98 0 (by decide +kernel)
  | exact S 10 98 1 (by decide +kernel)
  | exact S 10 98 2 (by decide +kernel)
  | exact S 10 98 3 (by decide +kernel)
  | exact S 10 98 4 (by decide +kernel)
  | exact S 10 98 5 (by decide +kernel)
theorem q10_99:ThresholdAt 10 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 99 0 (by decide +kernel)
  | exact S 10 99 1 (by decide +kernel)
  | exact S 10 99 2 (by decide +kernel)
  | exact S 10 99 3 (by decide +kernel)
  | exact S 10 99 4 (by decide +kernel)
  | exact S 10 99 5 (by decide +kernel)
theorem q10_100:ThresholdAt 10 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 100 0 (by decide +kernel)
  | exact S 10 100 1 (by decide +kernel)
  | exact S 10 100 2 (by decide +kernel)
  | exact S 10 100 3 (by decide +kernel)
  | exact S 10 100 4 (by decide +kernel)
  | exact S 10 100 5 (by decide +kernel)
theorem q10_101:ThresholdAt 10 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 101 0 (by decide +kernel)
  | exact S 10 101 1 (by decide +kernel)
  | exact S 10 101 2 (by decide +kernel)
  | exact S 10 101 3 (by decide +kernel)
  | exact S 10 101 4 (by decide +kernel)
  | exact S 10 101 5 (by decide +kernel)
theorem q10_102:ThresholdAt 10 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 102 0 (by decide +kernel)
  | exact S 10 102 1 (by decide +kernel)
  | exact S 10 102 2 (by decide +kernel)
  | exact S 10 102 3 (by decide +kernel)
  | exact S 10 102 4 (by decide +kernel)
  | exact S 10 102 5 (by decide +kernel)
theorem q10_103:ThresholdAt 10 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 103 0 (by decide +kernel)
  | exact S 10 103 1 (by decide +kernel)
  | exact S 10 103 2 (by decide +kernel)
  | exact S 10 103 3 (by decide +kernel)
  | exact S 10 103 4 (by decide +kernel)
  | exact S 10 103 5 (by decide +kernel)
theorem q10_104:ThresholdAt 10 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 104 0 (by decide +kernel)
  | exact S 10 104 1 (by decide +kernel)
  | exact S 10 104 2 (by decide +kernel)
  | exact S 10 104 3 (by decide +kernel)
  | exact S 10 104 4 (by decide +kernel)
  | exact S 10 104 5 (by decide +kernel)
theorem q10_105:ThresholdAt 10 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 105 0 (by decide +kernel)
  | exact S 10 105 1 (by decide +kernel)
  | exact S 10 105 2 (by decide +kernel)
  | exact S 10 105 3 (by decide +kernel)
  | exact S 10 105 4 (by decide +kernel)
  | exact S 10 105 5 (by decide +kernel)
theorem q10_106:ThresholdAt 10 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 106 0 (by decide +kernel)
  | exact S 10 106 1 (by decide +kernel)
  | exact S 10 106 2 (by decide +kernel)
  | exact S 10 106 3 (by decide +kernel)
  | exact S 10 106 4 (by decide +kernel)
  | exact S 10 106 5 (by decide +kernel)
theorem q10_107:ThresholdAt 10 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 107 0 (by decide +kernel)
  | exact S 10 107 1 (by decide +kernel)
  | exact S 10 107 2 (by decide +kernel)
  | exact S 10 107 3 (by decide +kernel)
  | exact S 10 107 4 (by decide +kernel)
  | exact S 10 107 5 (by decide +kernel)
theorem q10_108:ThresholdAt 10 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 108 0 (by decide +kernel)
  | exact S 10 108 1 (by decide +kernel)
  | exact S 10 108 2 (by decide +kernel)
  | exact S 10 108 3 (by decide +kernel)
  | exact S 10 108 4 (by decide +kernel)
  | exact S 10 108 5 (by decide +kernel)
theorem q10_109:ThresholdAt 10 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 109 0 (by decide +kernel)
  | exact S 10 109 1 (by decide +kernel)
  | exact S 10 109 2 (by decide +kernel)
  | exact S 10 109 3 (by decide +kernel)
  | exact S 10 109 4 (by decide +kernel)
  | exact S 10 109 5 (by decide +kernel)
theorem q10_110:ThresholdAt 10 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 110 0 (by decide +kernel)
  | exact S 10 110 1 (by decide +kernel)
  | exact S 10 110 2 (by decide +kernel)
  | exact S 10 110 3 (by decide +kernel)
  | exact S 10 110 4 (by decide +kernel)
  | exact S 10 110 5 (by decide +kernel)
theorem q10_111:ThresholdAt 10 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 111 0 (by decide +kernel)
  | exact S 10 111 1 (by decide +kernel)
  | exact S 10 111 2 (by decide +kernel)
  | exact S 10 111 3 (by decide +kernel)
  | exact S 10 111 4 (by decide +kernel)
  | exact S 10 111 5 (by decide +kernel)
theorem q10_112:ThresholdAt 10 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 112 0 (by decide +kernel)
  | exact S 10 112 1 (by decide +kernel)
  | exact S 10 112 2 (by decide +kernel)
  | exact S 10 112 3 (by decide +kernel)
  | exact S 10 112 4 (by decide +kernel)
  | exact S 10 112 5 (by decide +kernel)
theorem q10_113:ThresholdAt 10 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 113 0 (by decide +kernel)
  | exact S 10 113 1 (by decide +kernel)
  | exact S 10 113 2 (by decide +kernel)
  | exact S 10 113 3 (by decide +kernel)
  | exact S 10 113 4 (by decide +kernel)
  | exact S 10 113 5 (by decide +kernel)
theorem q10_114:ThresholdAt 10 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 114 0 (by decide +kernel)
  | exact S 10 114 1 (by decide +kernel)
  | exact S 10 114 2 (by decide +kernel)
  | exact S 10 114 3 (by decide +kernel)
  | exact S 10 114 4 (by decide +kernel)
  | exact S 10 114 5 (by decide +kernel)
theorem q10_115:ThresholdAt 10 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 115 0 (by decide +kernel)
  | exact S 10 115 1 (by decide +kernel)
  | exact S 10 115 2 (by decide +kernel)
  | exact S 10 115 3 (by decide +kernel)
  | exact S 10 115 4 (by decide +kernel)
  | exact S 10 115 5 (by decide +kernel)
theorem q10_116:ThresholdAt 10 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 116 0 (by decide +kernel)
  | exact S 10 116 1 (by decide +kernel)
  | exact S 10 116 2 (by decide +kernel)
  | exact S 10 116 3 (by decide +kernel)
  | exact S 10 116 4 (by decide +kernel)
  | exact S 10 116 5 (by decide +kernel)
theorem q10_117:ThresholdAt 10 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 117 0 (by decide +kernel)
  | exact S 10 117 1 (by decide +kernel)
  | exact S 10 117 2 (by decide +kernel)
  | exact S 10 117 3 (by decide +kernel)
  | exact S 10 117 4 (by decide +kernel)
  | exact S 10 117 5 (by decide +kernel)
theorem q10_118:ThresholdAt 10 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 118 0 (by decide +kernel)
  | exact S 10 118 1 (by decide +kernel)
  | exact S 10 118 2 (by decide +kernel)
  | exact S 10 118 3 (by decide +kernel)
  | exact S 10 118 4 (by decide +kernel)
  | exact S 10 118 5 (by decide +kernel)
theorem q10_119:ThresholdAt 10 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 119 0 (by decide +kernel)
  | exact S 10 119 1 (by decide +kernel)
  | exact S 10 119 2 (by decide +kernel)
  | exact S 10 119 3 (by decide +kernel)
  | exact S 10 119 4 (by decide +kernel)
  | exact S 10 119 5 (by decide +kernel)
theorem q10_120:ThresholdAt 10 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 120 0 (by decide +kernel)
  | exact S 10 120 1 (by decide +kernel)
  | exact S 10 120 2 (by decide +kernel)
  | exact S 10 120 3 (by decide +kernel)
  | exact S 10 120 4 (by decide +kernel)
  | exact S 10 120 5 (by decide +kernel)
theorem q10_121:ThresholdAt 10 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 121 0 (by decide +kernel)
  | exact S 10 121 1 (by decide +kernel)
  | exact S 10 121 2 (by decide +kernel)
  | exact S 10 121 3 (by decide +kernel)
  | exact S 10 121 4 (by decide +kernel)
  | exact S 10 121 5 (by decide +kernel)
theorem q10_122:ThresholdAt 10 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 122 0 (by decide +kernel)
  | exact S 10 122 1 (by decide +kernel)
  | exact S 10 122 2 (by decide +kernel)
  | exact S 10 122 3 (by decide +kernel)
  | exact S 10 122 4 (by decide +kernel)
  | exact S 10 122 5 (by decide +kernel)
theorem q10_123:ThresholdAt 10 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 123 0 (by decide +kernel)
  | exact S 10 123 1 (by decide +kernel)
  | exact S 10 123 2 (by decide +kernel)
  | exact S 10 123 3 (by decide +kernel)
  | exact S 10 123 4 (by decide +kernel)
  | exact S 10 123 5 (by decide +kernel)
theorem q10_124:ThresholdAt 10 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 124 0 (by decide +kernel)
  | exact S 10 124 1 (by decide +kernel)
  | exact S 10 124 2 (by decide +kernel)
  | exact S 10 124 3 (by decide +kernel)
  | exact S 10 124 4 (by decide +kernel)
  | exact S 10 124 5 (by decide +kernel)
theorem q10_125:ThresholdAt 10 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 125 0 (by decide +kernel)
  | exact S 10 125 1 (by decide +kernel)
  | exact S 10 125 2 (by decide +kernel)
  | exact S 10 125 3 (by decide +kernel)
  | exact S 10 125 4 (by decide +kernel)
  | exact S 10 125 5 (by decide +kernel)
theorem q10_126:ThresholdAt 10 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 126 0 (by decide +kernel)
  | exact S 10 126 1 (by decide +kernel)
  | exact S 10 126 2 (by decide +kernel)
  | exact S 10 126 3 (by decide +kernel)
  | exact S 10 126 4 (by decide +kernel)
  | exact S 10 126 5 (by decide +kernel)
theorem q10_127:ThresholdAt 10 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 127 0 (by decide +kernel)
  | exact S 10 127 1 (by decide +kernel)
  | exact S 10 127 2 (by decide +kernel)
  | exact S 10 127 3 (by decide +kernel)
  | exact S 10 127 4 (by decide +kernel)
  | exact S 10 127 5 (by decide +kernel)
theorem q10_128:ThresholdAt 10 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 128 0 (by decide +kernel)
  | exact S 10 128 1 (by decide +kernel)
  | exact S 10 128 2 (by decide +kernel)
  | exact S 10 128 3 (by decide +kernel)
  | exact S 10 128 4 (by decide +kernel)
  | exact S 10 128 5 (by decide +kernel)
theorem q10_129:ThresholdAt 10 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 129 0 (by decide +kernel)
  | exact S 10 129 1 (by decide +kernel)
  | exact S 10 129 2 (by decide +kernel)
  | exact S 10 129 3 (by decide +kernel)
  | exact S 10 129 4 (by decide +kernel)
  | exact S 10 129 5 (by decide +kernel)
theorem q10_130:ThresholdAt 10 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 130 0 (by decide +kernel)
  | exact S 10 130 1 (by decide +kernel)
  | exact S 10 130 2 (by decide +kernel)
  | exact S 10 130 3 (by decide +kernel)
  | exact S 10 130 4 (by decide +kernel)
  | exact S 10 130 5 (by decide +kernel)
theorem q10_131:ThresholdAt 10 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 131 0 (by decide +kernel)
  | exact S 10 131 1 (by decide +kernel)
  | exact S 10 131 2 (by decide +kernel)
  | exact S 10 131 3 (by decide +kernel)
  | exact S 10 131 4 (by decide +kernel)
  | exact S 10 131 5 (by decide +kernel)
theorem q10_132:ThresholdAt 10 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 10 132 0 (by decide +kernel)
  | exact S 10 132 1 (by decide +kernel)
  | exact S 10 132 2 (by decide +kernel)
  | exact S 10 132 3 (by decide +kernel)
  | exact S 10 132 4 (by decide +kernel)
  | exact S 10 132 5 (by decide +kernel)
theorem checkedR10:∀ V ∈ List.range 133,ThresholdAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0_133:V < 66
  · by_cases h0_66:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q10_0
              · have he:V = 1:=by omega
                subst V
                exact q10_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q10_2
              · have he:V = 3:=by omega
                subst V
                exact q10_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q10_4
              · have he:V = 5:=by omega
                subst V
                exact q10_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q10_6
              · have he:V = 7:=by omega
                subst V
                exact q10_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q10_8
              · have he:V = 9:=by omega
                subst V
                exact q10_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q10_10
              · have he:V = 11:=by omega
                subst V
                exact q10_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q10_12
              · have he:V = 13:=by omega
                subst V
                exact q10_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q10_14
              · have he:V = 15:=by omega
                subst V
                exact q10_15
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q10_16
              · have he:V = 17:=by omega
                subst V
                exact q10_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q10_18
              · have he:V = 19:=by omega
                subst V
                exact q10_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q10_20
              · have he:V = 21:=by omega
                subst V
                exact q10_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q10_22
              · have he:V = 23:=by omega
                subst V
                exact q10_23
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q10_24
              · have he:V = 25:=by omega
                subst V
                exact q10_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q10_26
              · have he:V = 27:=by omega
                subst V
                exact q10_27
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q10_28
              · have he:V = 29:=by omega
                subst V
                exact q10_29
            · by_cases h30_33:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q10_30
              · by_cases h31_33:V < 32
                · have he:V = 31:=by omega
                  subst V
                  exact q10_31
                · have he:V = 32:=by omega
                  subst V
                  exact q10_32
    · by_cases h33_66:V < 49
      · by_cases h33_49:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q10_33
              · have he:V = 34:=by omega
                subst V
                exact q10_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q10_35
              · have he:V = 36:=by omega
                subst V
                exact q10_36
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q10_37
              · have he:V = 38:=by omega
                subst V
                exact q10_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q10_39
              · have he:V = 40:=by omega
                subst V
                exact q10_40
        · by_cases h41_49:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q10_41
              · have he:V = 42:=by omega
                subst V
                exact q10_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q10_43
              · have he:V = 44:=by omega
                subst V
                exact q10_44
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q10_45
              · have he:V = 46:=by omega
                subst V
                exact q10_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q10_47
              · have he:V = 48:=by omega
                subst V
                exact q10_48
      · by_cases h49_66:V < 57
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q10_49
              · have he:V = 50:=by omega
                subst V
                exact q10_50
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q10_51
              · have he:V = 52:=by omega
                subst V
                exact q10_52
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q10_53
              · have he:V = 54:=by omega
                subst V
                exact q10_54
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q10_55
              · have he:V = 56:=by omega
                subst V
                exact q10_56
        · by_cases h57_66:V < 61
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q10_57
              · have he:V = 58:=by omega
                subst V
                exact q10_58
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q10_59
              · have he:V = 60:=by omega
                subst V
                exact q10_60
          · by_cases h61_66:V < 63
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q10_61
              · have he:V = 62:=by omega
                subst V
                exact q10_62
            · by_cases h63_66:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q10_63
              · by_cases h64_66:V < 65
                · have he:V = 64:=by omega
                  subst V
                  exact q10_64
                · have he:V = 65:=by omega
                  subst V
                  exact q10_65
  · by_cases h66_133:V < 99
    · by_cases h66_99:V < 82
      · by_cases h66_82:V < 74
        · by_cases h66_74:V < 70
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q10_66
              · have he:V = 67:=by omega
                subst V
                exact q10_67
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q10_68
              · have he:V = 69:=by omega
                subst V
                exact q10_69
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q10_70
              · have he:V = 71:=by omega
                subst V
                exact q10_71
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q10_72
              · have he:V = 73:=by omega
                subst V
                exact q10_73
        · by_cases h74_82:V < 78
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q10_74
              · have he:V = 75:=by omega
                subst V
                exact q10_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q10_76
              · have he:V = 77:=by omega
                subst V
                exact q10_77
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q10_78
              · have he:V = 79:=by omega
                subst V
                exact q10_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q10_80
              · have he:V = 81:=by omega
                subst V
                exact q10_81
      · by_cases h82_99:V < 90
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q10_82
              · have he:V = 83:=by omega
                subst V
                exact q10_83
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q10_84
              · have he:V = 85:=by omega
                subst V
                exact q10_85
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q10_86
              · have he:V = 87:=by omega
                subst V
                exact q10_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q10_88
              · have he:V = 89:=by omega
                subst V
                exact q10_89
        · by_cases h90_99:V < 94
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q10_90
              · have he:V = 91:=by omega
                subst V
                exact q10_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q10_92
              · have he:V = 93:=by omega
                subst V
                exact q10_93
          · by_cases h94_99:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q10_94
              · have he:V = 95:=by omega
                subst V
                exact q10_95
            · by_cases h96_99:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q10_96
              · by_cases h97_99:V < 98
                · have he:V = 97:=by omega
                  subst V
                  exact q10_97
                · have he:V = 98:=by omega
                  subst V
                  exact q10_98
    · by_cases h99_133:V < 116
      · by_cases h99_116:V < 107
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q10_99
              · have he:V = 100:=by omega
                subst V
                exact q10_100
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q10_101
              · have he:V = 102:=by omega
                subst V
                exact q10_102
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q10_103
              · have he:V = 104:=by omega
                subst V
                exact q10_104
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q10_105
              · have he:V = 106:=by omega
                subst V
                exact q10_106
        · by_cases h107_116:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q10_107
              · have he:V = 108:=by omega
                subst V
                exact q10_108
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q10_109
              · have he:V = 110:=by omega
                subst V
                exact q10_110
          · by_cases h111_116:V < 113
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q10_111
              · have he:V = 112:=by omega
                subst V
                exact q10_112
            · by_cases h113_116:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q10_113
              · by_cases h114_116:V < 115
                · have he:V = 114:=by omega
                  subst V
                  exact q10_114
                · have he:V = 115:=by omega
                  subst V
                  exact q10_115
      · by_cases h116_133:V < 124
        · by_cases h116_124:V < 120
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q10_116
              · have he:V = 117:=by omega
                subst V
                exact q10_117
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q10_118
              · have he:V = 119:=by omega
                subst V
                exact q10_119
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q10_120
              · have he:V = 121:=by omega
                subst V
                exact q10_121
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q10_122
              · have he:V = 123:=by omega
                subst V
                exact q10_123
        · by_cases h124_133:V < 128
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q10_124
              · have he:V = 125:=by omega
                subst V
                exact q10_125
            · by_cases h126_128:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q10_126
              · have he:V = 127:=by omega
                subst V
                exact q10_127
          · by_cases h128_133:V < 130
            · by_cases h128_130:V < 129
              · have he:V = 128:=by omega
                subst V
                exact q10_128
              · have he:V = 129:=by omega
                subst V
                exact q10_129
            · by_cases h130_133:V < 131
              · have he:V = 130:=by omega
                subst V
                exact q10_130
              · by_cases h131_133:V < 132
                · have he:V = 131:=by omega
                  subst V
                  exact q10_131
                · have he:V = 132:=by omega
                  subst V
                  exact q10_132
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
