import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked17

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q18_0:ThresholdAt 18 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 0 0 (by decide +kernel)
  | exact S 18 0 1 (by decide +kernel)
  | exact S 18 0 2 (by decide +kernel)
  | exact S 18 0 3 (by decide +kernel)
  | exact S 18 0 4 (by decide +kernel)
  | exact S 18 0 5 (by decide +kernel)
theorem q18_1:ThresholdAt 18 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 1 0 (by decide +kernel)
  | exact S 18 1 1 (by decide +kernel)
  | exact S 18 1 2 (by decide +kernel)
  | exact S 18 1 3 (by decide +kernel)
  | exact S 18 1 4 (by decide +kernel)
  | exact S 18 1 5 (by decide +kernel)
theorem q18_2:ThresholdAt 18 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 2 0 (by decide +kernel)
  | exact S 18 2 1 (by decide +kernel)
  | exact S 18 2 2 (by decide +kernel)
  | exact S 18 2 3 (by decide +kernel)
  | exact S 18 2 4 (by decide +kernel)
  | exact S 18 2 5 (by decide +kernel)
theorem q18_3:ThresholdAt 18 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 3 0 (by decide +kernel)
  | exact S 18 3 1 (by decide +kernel)
  | exact S 18 3 2 (by decide +kernel)
  | exact S 18 3 3 (by decide +kernel)
  | exact S 18 3 4 (by decide +kernel)
  | exact S 18 3 5 (by decide +kernel)
theorem q18_4:ThresholdAt 18 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 4 0 (by decide +kernel)
  | exact S 18 4 1 (by decide +kernel)
  | exact S 18 4 2 (by decide +kernel)
  | exact S 18 4 3 (by decide +kernel)
  | exact S 18 4 4 (by decide +kernel)
  | exact S 18 4 5 (by decide +kernel)
theorem q18_5:ThresholdAt 18 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 5 0 (by decide +kernel)
  | exact S 18 5 1 (by decide +kernel)
  | exact S 18 5 2 (by decide +kernel)
  | exact S 18 5 3 (by decide +kernel)
  | exact S 18 5 4 (by decide +kernel)
  | exact S 18 5 5 (by decide +kernel)
theorem q18_6:ThresholdAt 18 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 6 0 (by decide +kernel)
  | exact S 18 6 1 (by decide +kernel)
  | exact S 18 6 2 (by decide +kernel)
  | exact S 18 6 3 (by decide +kernel)
  | exact S 18 6 4 (by decide +kernel)
  | exact S 18 6 5 (by decide +kernel)
theorem q18_7:ThresholdAt 18 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 7 0 (by decide +kernel)
  | exact S 18 7 1 (by decide +kernel)
  | exact S 18 7 2 (by decide +kernel)
  | exact S 18 7 3 (by decide +kernel)
  | exact S 18 7 4 (by decide +kernel)
  | exact S 18 7 5 (by decide +kernel)
theorem q18_8:ThresholdAt 18 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 8 0 (by decide +kernel)
  | exact S 18 8 1 (by decide +kernel)
  | exact S 18 8 2 (by decide +kernel)
  | exact S 18 8 3 (by decide +kernel)
  | exact S 18 8 4 (by decide +kernel)
  | exact S 18 8 5 (by decide +kernel)
theorem q18_9:ThresholdAt 18 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 9 0 (by decide +kernel)
  | exact S 18 9 1 (by decide +kernel)
  | exact S 18 9 2 (by decide +kernel)
  | exact S 18 9 3 (by decide +kernel)
  | exact S 18 9 4 (by decide +kernel)
  | exact S 18 9 5 (by decide +kernel)
theorem q18_10:ThresholdAt 18 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 10 0 (by decide +kernel)
  | exact S 18 10 1 (by decide +kernel)
  | exact S 18 10 2 (by decide +kernel)
  | exact S 18 10 3 (by decide +kernel)
  | exact S 18 10 4 (by decide +kernel)
  | exact S 18 10 5 (by decide +kernel)
theorem q18_11:ThresholdAt 18 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 11 0 (by decide +kernel)
  | exact S 18 11 1 (by decide +kernel)
  | exact S 18 11 2 (by decide +kernel)
  | exact S 18 11 3 (by decide +kernel)
  | exact S 18 11 4 (by decide +kernel)
  | exact S 18 11 5 (by decide +kernel)
theorem q18_12:ThresholdAt 18 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 12 0 (by decide +kernel)
  | exact S 18 12 1 (by decide +kernel)
  | exact S 18 12 2 (by decide +kernel)
  | exact S 18 12 3 (by decide +kernel)
  | exact S 18 12 4 (by decide +kernel)
  | exact S 18 12 5 (by decide +kernel)
theorem q18_13:ThresholdAt 18 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 13 0 (by decide +kernel)
  | exact S 18 13 1 (by decide +kernel)
  | exact S 18 13 2 (by decide +kernel)
  | exact S 18 13 3 (by decide +kernel)
  | exact S 18 13 4 (by decide +kernel)
  | exact S 18 13 5 (by decide +kernel)
theorem q18_14:ThresholdAt 18 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 14 0 (by decide +kernel)
  | exact S 18 14 1 (by decide +kernel)
  | exact S 18 14 2 (by decide +kernel)
  | exact S 18 14 3 (by decide +kernel)
  | exact S 18 14 4 (by decide +kernel)
  | exact S 18 14 5 (by decide +kernel)
theorem q18_15:ThresholdAt 18 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 15 0 (by decide +kernel)
  | exact S 18 15 1 (by decide +kernel)
  | exact S 18 15 2 (by decide +kernel)
  | exact S 18 15 3 (by decide +kernel)
  | exact S 18 15 4 (by decide +kernel)
  | exact S 18 15 5 (by decide +kernel)
theorem q18_16:ThresholdAt 18 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 16 0 (by decide +kernel)
  | exact S 18 16 1 (by decide +kernel)
  | exact S 18 16 2 (by decide +kernel)
  | exact S 18 16 3 (by decide +kernel)
  | exact S 18 16 4 (by decide +kernel)
  | exact S 18 16 5 (by decide +kernel)
theorem q18_17:ThresholdAt 18 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 17 0 (by decide +kernel)
  | exact S 18 17 1 (by decide +kernel)
  | exact S 18 17 2 (by decide +kernel)
  | exact S 18 17 3 (by decide +kernel)
  | exact S 18 17 4 (by decide +kernel)
  | exact S 18 17 5 (by decide +kernel)
theorem q18_18:ThresholdAt 18 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 18 0 (by decide +kernel)
  | exact S 18 18 1 (by decide +kernel)
  | exact S 18 18 2 (by decide +kernel)
  | exact S 18 18 3 (by decide +kernel)
  | exact S 18 18 4 (by decide +kernel)
  | exact S 18 18 5 (by decide +kernel)
theorem q18_19:ThresholdAt 18 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 19 0 (by decide +kernel)
  | exact S 18 19 1 (by decide +kernel)
  | exact S 18 19 2 (by decide +kernel)
  | exact S 18 19 3 (by decide +kernel)
  | exact S 18 19 4 (by decide +kernel)
  | exact S 18 19 5 (by decide +kernel)
theorem q18_20:ThresholdAt 18 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 20 0 (by decide +kernel)
  | exact S 18 20 1 (by decide +kernel)
  | exact S 18 20 2 (by decide +kernel)
  | exact S 18 20 3 (by decide +kernel)
  | exact S 18 20 4 (by decide +kernel)
  | exact S 18 20 5 (by decide +kernel)
theorem q18_21:ThresholdAt 18 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 21 0 (by decide +kernel)
  | exact S 18 21 1 (by decide +kernel)
  | exact S 18 21 2 (by decide +kernel)
  | exact S 18 21 3 (by decide +kernel)
  | exact S 18 21 4 (by decide +kernel)
  | exact S 18 21 5 (by decide +kernel)
theorem q18_22:ThresholdAt 18 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 22 0 (by decide +kernel)
  | exact S 18 22 1 (by decide +kernel)
  | exact S 18 22 2 (by decide +kernel)
  | exact S 18 22 3 (by decide +kernel)
  | exact S 18 22 4 (by decide +kernel)
  | exact S 18 22 5 (by decide +kernel)
theorem q18_23:ThresholdAt 18 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 23 0 (by decide +kernel)
  | exact S 18 23 1 (by decide +kernel)
  | exact S 18 23 2 (by decide +kernel)
  | exact S 18 23 3 (by decide +kernel)
  | exact S 18 23 4 (by decide +kernel)
  | exact S 18 23 5 (by decide +kernel)
theorem q18_24:ThresholdAt 18 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 24 0 (by decide +kernel)
  | exact S 18 24 1 (by decide +kernel)
  | exact S 18 24 2 (by decide +kernel)
  | exact S 18 24 3 (by decide +kernel)
  | exact S 18 24 4 (by decide +kernel)
  | exact S 18 24 5 (by decide +kernel)
theorem q18_25:ThresholdAt 18 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 25 0 (by decide +kernel)
  | exact S 18 25 1 (by decide +kernel)
  | exact S 18 25 2 (by decide +kernel)
  | exact S 18 25 3 (by decide +kernel)
  | exact S 18 25 4 (by decide +kernel)
  | exact S 18 25 5 (by decide +kernel)
theorem q18_26:ThresholdAt 18 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 26 0 (by decide +kernel)
  | exact S 18 26 1 (by decide +kernel)
  | exact S 18 26 2 (by decide +kernel)
  | exact S 18 26 3 (by decide +kernel)
  | exact S 18 26 4 (by decide +kernel)
  | exact S 18 26 5 (by decide +kernel)
theorem q18_27:ThresholdAt 18 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 27 0 (by decide +kernel)
  | exact S 18 27 1 (by decide +kernel)
  | exact S 18 27 2 (by decide +kernel)
  | exact S 18 27 3 (by decide +kernel)
  | exact S 18 27 4 (by decide +kernel)
  | exact S 18 27 5 (by decide +kernel)
theorem q18_28:ThresholdAt 18 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 28 0 (by decide +kernel)
  | exact S 18 28 1 (by decide +kernel)
  | exact S 18 28 2 (by decide +kernel)
  | exact S 18 28 3 (by decide +kernel)
  | exact S 18 28 4 (by decide +kernel)
  | exact S 18 28 5 (by decide +kernel)
theorem q18_29:ThresholdAt 18 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 29 0 (by decide +kernel)
  | exact S 18 29 1 (by decide +kernel)
  | exact S 18 29 2 (by decide +kernel)
  | exact S 18 29 3 (by decide +kernel)
  | exact S 18 29 4 (by decide +kernel)
  | exact S 18 29 5 (by decide +kernel)
theorem q18_30:ThresholdAt 18 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 30 0 (by decide +kernel)
  | exact S 18 30 1 (by decide +kernel)
  | exact S 18 30 2 (by decide +kernel)
  | exact S 18 30 3 (by decide +kernel)
  | exact S 18 30 4 (by decide +kernel)
  | exact S 18 30 5 (by decide +kernel)
theorem q18_31:ThresholdAt 18 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 31 0 (by decide +kernel)
  | exact S 18 31 1 (by decide +kernel)
  | exact S 18 31 2 (by decide +kernel)
  | exact S 18 31 3 (by decide +kernel)
  | exact S 18 31 4 (by decide +kernel)
  | exact S 18 31 5 (by decide +kernel)
theorem q18_32:ThresholdAt 18 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 32 0 (by decide +kernel)
  | exact S 18 32 1 (by decide +kernel)
  | exact S 18 32 2 (by decide +kernel)
  | exact S 18 32 3 (by decide +kernel)
  | exact S 18 32 4 (by decide +kernel)
  | exact S 18 32 5 (by decide +kernel)
theorem q18_33:ThresholdAt 18 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 33 0 (by decide +kernel)
  | exact S 18 33 1 (by decide +kernel)
  | exact S 18 33 2 (by decide +kernel)
  | exact S 18 33 3 (by decide +kernel)
  | exact S 18 33 4 (by decide +kernel)
  | exact S 18 33 5 (by decide +kernel)
theorem q18_34:ThresholdAt 18 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 34 0 (by decide +kernel)
  | exact S 18 34 1 (by decide +kernel)
  | exact S 18 34 2 (by decide +kernel)
  | exact S 18 34 3 (by decide +kernel)
  | exact S 18 34 4 (by decide +kernel)
  | exact S 18 34 5 (by decide +kernel)
theorem q18_35:ThresholdAt 18 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 35 0 (by decide +kernel)
  | exact S 18 35 1 (by decide +kernel)
  | exact S 18 35 2 (by decide +kernel)
  | exact S 18 35 3 (by decide +kernel)
  | exact S 18 35 4 (by decide +kernel)
  | exact S 18 35 5 (by decide +kernel)
theorem q18_36:ThresholdAt 18 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 36 0 (by decide +kernel)
  | exact S 18 36 1 (by decide +kernel)
  | exact S 18 36 2 (by decide +kernel)
  | exact S 18 36 3 (by decide +kernel)
  | exact S 18 36 4 (by decide +kernel)
  | exact S 18 36 5 (by decide +kernel)
theorem q18_37:ThresholdAt 18 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 37 0 (by decide +kernel)
  | exact S 18 37 1 (by decide +kernel)
  | exact S 18 37 2 (by decide +kernel)
  | exact S 18 37 3 (by decide +kernel)
  | exact S 18 37 4 (by decide +kernel)
  | exact S 18 37 5 (by decide +kernel)
theorem q18_38:ThresholdAt 18 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 38 0 (by decide +kernel)
  | exact S 18 38 1 (by decide +kernel)
  | exact S 18 38 2 (by decide +kernel)
  | exact S 18 38 3 (by decide +kernel)
  | exact S 18 38 4 (by decide +kernel)
  | exact S 18 38 5 (by decide +kernel)
theorem q18_39:ThresholdAt 18 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 39 0 (by decide +kernel)
  | exact S 18 39 1 (by decide +kernel)
  | exact S 18 39 2 (by decide +kernel)
  | exact S 18 39 3 (by decide +kernel)
  | exact S 18 39 4 (by decide +kernel)
  | exact S 18 39 5 (by decide +kernel)
theorem q18_40:ThresholdAt 18 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 40 0 (by decide +kernel)
  | exact S 18 40 1 (by decide +kernel)
  | exact S 18 40 2 (by decide +kernel)
  | exact S 18 40 3 (by decide +kernel)
  | exact S 18 40 4 (by decide +kernel)
  | exact S 18 40 5 (by decide +kernel)
theorem q18_41:ThresholdAt 18 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 41 0 (by decide +kernel)
  | exact S 18 41 1 (by decide +kernel)
  | exact S 18 41 2 (by decide +kernel)
  | exact S 18 41 3 (by decide +kernel)
  | exact S 18 41 4 (by decide +kernel)
  | exact S 18 41 5 (by decide +kernel)
theorem q18_42:ThresholdAt 18 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 42 0 (by decide +kernel)
  | exact S 18 42 1 (by decide +kernel)
  | exact S 18 42 2 (by decide +kernel)
  | exact S 18 42 3 (by decide +kernel)
  | exact S 18 42 4 (by decide +kernel)
  | exact S 18 42 5 (by decide +kernel)
theorem q18_43:ThresholdAt 18 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 43 0 (by decide +kernel)
  | exact S 18 43 1 (by decide +kernel)
  | exact S 18 43 2 (by decide +kernel)
  | exact S 18 43 3 (by decide +kernel)
  | exact S 18 43 4 (by decide +kernel)
  | exact S 18 43 5 (by decide +kernel)
theorem q18_44:ThresholdAt 18 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 44 0 (by decide +kernel)
  | exact S 18 44 1 (by decide +kernel)
  | exact S 18 44 2 (by decide +kernel)
  | exact S 18 44 3 (by decide +kernel)
  | exact S 18 44 4 (by decide +kernel)
  | exact S 18 44 5 (by decide +kernel)
theorem q18_45:ThresholdAt 18 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 45 0 (by decide +kernel)
  | exact S 18 45 1 (by decide +kernel)
  | exact S 18 45 2 (by decide +kernel)
  | exact S 18 45 3 (by decide +kernel)
  | exact S 18 45 4 (by decide +kernel)
  | exact S 18 45 5 (by decide +kernel)
theorem q18_46:ThresholdAt 18 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 46 0 (by decide +kernel)
  | exact S 18 46 1 (by decide +kernel)
  | exact S 18 46 2 (by decide +kernel)
  | exact S 18 46 3 (by decide +kernel)
  | exact S 18 46 4 (by decide +kernel)
  | exact S 18 46 5 (by decide +kernel)
theorem q18_47:ThresholdAt 18 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 47 0 (by decide +kernel)
  | exact S 18 47 1 (by decide +kernel)
  | exact S 18 47 2 (by decide +kernel)
  | exact S 18 47 3 (by decide +kernel)
  | exact S 18 47 4 (by decide +kernel)
  | exact S 18 47 5 (by decide +kernel)
theorem q18_48:ThresholdAt 18 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 48 0 (by decide +kernel)
  | exact S 18 48 1 (by decide +kernel)
  | exact S 18 48 2 (by decide +kernel)
  | exact S 18 48 3 (by decide +kernel)
  | exact S 18 48 4 (by decide +kernel)
  | exact S 18 48 5 (by decide +kernel)
theorem q18_49:ThresholdAt 18 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 49 0 (by decide +kernel)
  | exact S 18 49 1 (by decide +kernel)
  | exact S 18 49 2 (by decide +kernel)
  | exact S 18 49 3 (by decide +kernel)
  | exact S 18 49 4 (by decide +kernel)
  | exact S 18 49 5 (by decide +kernel)
theorem q18_50:ThresholdAt 18 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 50 0 (by decide +kernel)
  | exact S 18 50 1 (by decide +kernel)
  | exact S 18 50 2 (by decide +kernel)
  | exact S 18 50 3 (by decide +kernel)
  | exact S 18 50 4 (by decide +kernel)
  | exact S 18 50 5 (by decide +kernel)
theorem q18_51:ThresholdAt 18 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 51 0 (by decide +kernel)
  | exact S 18 51 1 (by decide +kernel)
  | exact S 18 51 2 (by decide +kernel)
  | exact S 18 51 3 (by decide +kernel)
  | exact S 18 51 4 (by decide +kernel)
  | exact S 18 51 5 (by decide +kernel)
theorem q18_52:ThresholdAt 18 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 52 0 (by decide +kernel)
  | exact S 18 52 1 (by decide +kernel)
  | exact S 18 52 2 (by decide +kernel)
  | exact S 18 52 3 (by decide +kernel)
  | exact S 18 52 4 (by decide +kernel)
  | exact S 18 52 5 (by decide +kernel)
theorem q18_53:ThresholdAt 18 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 53 0 (by decide +kernel)
  | exact S 18 53 1 (by decide +kernel)
  | exact S 18 53 2 (by decide +kernel)
  | exact S 18 53 3 (by decide +kernel)
  | exact S 18 53 4 (by decide +kernel)
  | exact S 18 53 5 (by decide +kernel)
theorem q18_54:ThresholdAt 18 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 54 0 (by decide +kernel)
  | exact S 18 54 1 (by decide +kernel)
  | exact S 18 54 2 (by decide +kernel)
  | exact S 18 54 3 (by decide +kernel)
  | exact S 18 54 4 (by decide +kernel)
  | exact S 18 54 5 (by decide +kernel)
theorem q18_55:ThresholdAt 18 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 55 0 (by decide +kernel)
  | exact S 18 55 1 (by decide +kernel)
  | exact S 18 55 2 (by decide +kernel)
  | exact S 18 55 3 (by decide +kernel)
  | exact S 18 55 4 (by decide +kernel)
  | exact S 18 55 5 (by decide +kernel)
theorem q18_56:ThresholdAt 18 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 56 0 (by decide +kernel)
  | exact S 18 56 1 (by decide +kernel)
  | exact S 18 56 2 (by decide +kernel)
  | exact S 18 56 3 (by decide +kernel)
  | exact S 18 56 4 (by decide +kernel)
  | exact S 18 56 5 (by decide +kernel)
theorem q18_57:ThresholdAt 18 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 57 0 (by decide +kernel)
  | exact S 18 57 1 (by decide +kernel)
  | exact S 18 57 2 (by decide +kernel)
  | exact S 18 57 3 (by decide +kernel)
  | exact S 18 57 4 (by decide +kernel)
  | exact S 18 57 5 (by decide +kernel)
theorem q18_58:ThresholdAt 18 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 58 0 (by decide +kernel)
  | exact S 18 58 1 (by decide +kernel)
  | exact S 18 58 2 (by decide +kernel)
  | exact S 18 58 3 (by decide +kernel)
  | exact S 18 58 4 (by decide +kernel)
  | exact S 18 58 5 (by decide +kernel)
theorem q18_59:ThresholdAt 18 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 59 0 (by decide +kernel)
  | exact S 18 59 1 (by decide +kernel)
  | exact S 18 59 2 (by decide +kernel)
  | exact S 18 59 3 (by decide +kernel)
  | exact S 18 59 4 (by decide +kernel)
  | exact S 18 59 5 (by decide +kernel)
theorem q18_60:ThresholdAt 18 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 60 0 (by decide +kernel)
  | exact S 18 60 1 (by decide +kernel)
  | exact S 18 60 2 (by decide +kernel)
  | exact S 18 60 3 (by decide +kernel)
  | exact S 18 60 4 (by decide +kernel)
  | exact S 18 60 5 (by decide +kernel)
theorem q18_61:ThresholdAt 18 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 61 0 (by decide +kernel)
  | exact S 18 61 1 (by decide +kernel)
  | exact S 18 61 2 (by decide +kernel)
  | exact S 18 61 3 (by decide +kernel)
  | exact S 18 61 4 (by decide +kernel)
  | exact S 18 61 5 (by decide +kernel)
theorem q18_62:ThresholdAt 18 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 62 0 (by decide +kernel)
  | exact S 18 62 1 (by decide +kernel)
  | exact S 18 62 2 (by decide +kernel)
  | exact S 18 62 3 (by decide +kernel)
  | exact S 18 62 4 (by decide +kernel)
  | exact S 18 62 5 (by decide +kernel)
theorem q18_63:ThresholdAt 18 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 63 0 (by decide +kernel)
  | exact S 18 63 1 (by decide +kernel)
  | exact S 18 63 2 (by decide +kernel)
  | exact S 18 63 3 (by decide +kernel)
  | exact S 18 63 4 (by decide +kernel)
  | exact S 18 63 5 (by decide +kernel)
theorem q18_64:ThresholdAt 18 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 64 0 (by decide +kernel)
  | exact S 18 64 1 (by decide +kernel)
  | exact S 18 64 2 (by decide +kernel)
  | exact S 18 64 3 (by decide +kernel)
  | exact S 18 64 4 (by decide +kernel)
  | exact S 18 64 5 (by decide +kernel)
theorem q18_65:ThresholdAt 18 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 65 0 (by decide +kernel)
  | exact S 18 65 1 (by decide +kernel)
  | exact S 18 65 2 (by decide +kernel)
  | exact S 18 65 3 (by decide +kernel)
  | exact S 18 65 4 (by decide +kernel)
  | exact S 18 65 5 (by decide +kernel)
theorem q18_66:ThresholdAt 18 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 66 0 (by decide +kernel)
  | exact S 18 66 1 (by decide +kernel)
  | exact S 18 66 2 (by decide +kernel)
  | exact S 18 66 3 (by decide +kernel)
  | exact S 18 66 4 (by decide +kernel)
  | exact S 18 66 5 (by decide +kernel)
theorem q18_67:ThresholdAt 18 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 67 0 (by decide +kernel)
  | exact S 18 67 1 (by decide +kernel)
  | exact S 18 67 2 (by decide +kernel)
  | exact S 18 67 3 (by decide +kernel)
  | exact S 18 67 4 (by decide +kernel)
  | exact S 18 67 5 (by decide +kernel)
theorem q18_68:ThresholdAt 18 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 68 0 (by decide +kernel)
  | exact S 18 68 1 (by decide +kernel)
  | exact S 18 68 2 (by decide +kernel)
  | exact S 18 68 3 (by decide +kernel)
  | exact S 18 68 4 (by decide +kernel)
  | exact S 18 68 5 (by decide +kernel)
theorem q18_69:ThresholdAt 18 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 69 0 (by decide +kernel)
  | exact S 18 69 1 (by decide +kernel)
  | exact S 18 69 2 (by decide +kernel)
  | exact S 18 69 3 (by decide +kernel)
  | exact S 18 69 4 (by decide +kernel)
  | exact S 18 69 5 (by decide +kernel)
theorem q18_70:ThresholdAt 18 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 70 0 (by decide +kernel)
  | exact S 18 70 1 (by decide +kernel)
  | exact S 18 70 2 (by decide +kernel)
  | exact S 18 70 3 (by decide +kernel)
  | exact S 18 70 4 (by decide +kernel)
  | exact S 18 70 5 (by decide +kernel)
theorem q18_71:ThresholdAt 18 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 71 0 (by decide +kernel)
  | exact S 18 71 1 (by decide +kernel)
  | exact S 18 71 2 (by decide +kernel)
  | exact S 18 71 3 (by decide +kernel)
  | exact S 18 71 4 (by decide +kernel)
  | exact S 18 71 5 (by decide +kernel)
theorem q18_72:ThresholdAt 18 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 72 0 (by decide +kernel)
  | exact S 18 72 1 (by decide +kernel)
  | exact S 18 72 2 (by decide +kernel)
  | exact S 18 72 3 (by decide +kernel)
  | exact S 18 72 4 (by decide +kernel)
  | exact S 18 72 5 (by decide +kernel)
theorem q18_73:ThresholdAt 18 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 73 0 (by decide +kernel)
  | exact S 18 73 1 (by decide +kernel)
  | exact S 18 73 2 (by decide +kernel)
  | exact S 18 73 3 (by decide +kernel)
  | exact S 18 73 4 (by decide +kernel)
  | exact S 18 73 5 (by decide +kernel)
theorem q18_74:ThresholdAt 18 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 74 0 (by decide +kernel)
  | exact S 18 74 1 (by decide +kernel)
  | exact S 18 74 2 (by decide +kernel)
  | exact S 18 74 3 (by decide +kernel)
  | exact S 18 74 4 (by decide +kernel)
  | exact S 18 74 5 (by decide +kernel)
theorem q18_75:ThresholdAt 18 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 75 0 (by decide +kernel)
  | exact S 18 75 1 (by decide +kernel)
  | exact S 18 75 2 (by decide +kernel)
  | exact S 18 75 3 (by decide +kernel)
  | exact S 18 75 4 (by decide +kernel)
  | exact S 18 75 5 (by decide +kernel)
theorem q18_76:ThresholdAt 18 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 76 0 (by decide +kernel)
  | exact S 18 76 1 (by decide +kernel)
  | exact S 18 76 2 (by decide +kernel)
  | exact S 18 76 3 (by decide +kernel)
  | exact S 18 76 4 (by decide +kernel)
  | exact S 18 76 5 (by decide +kernel)
theorem q18_77:ThresholdAt 18 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 77 0 (by decide +kernel)
  | exact S 18 77 1 (by decide +kernel)
  | exact S 18 77 2 (by decide +kernel)
  | exact S 18 77 3 (by decide +kernel)
  | exact S 18 77 4 (by decide +kernel)
  | exact S 18 77 5 (by decide +kernel)
theorem q18_78:ThresholdAt 18 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 78 0 (by decide +kernel)
  | exact S 18 78 1 (by decide +kernel)
  | exact S 18 78 2 (by decide +kernel)
  | exact S 18 78 3 (by decide +kernel)
  | exact S 18 78 4 (by decide +kernel)
  | exact S 18 78 5 (by decide +kernel)
theorem q18_79:ThresholdAt 18 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 79 0 (by decide +kernel)
  | exact S 18 79 1 (by decide +kernel)
  | exact S 18 79 2 (by decide +kernel)
  | exact S 18 79 3 (by decide +kernel)
  | exact S 18 79 4 (by decide +kernel)
  | exact S 18 79 5 (by decide +kernel)
theorem q18_80:ThresholdAt 18 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 80 0 (by decide +kernel)
  | exact S 18 80 1 (by decide +kernel)
  | exact S 18 80 2 (by decide +kernel)
  | exact S 18 80 3 (by decide +kernel)
  | exact S 18 80 4 (by decide +kernel)
  | exact S 18 80 5 (by decide +kernel)
theorem q18_81:ThresholdAt 18 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 81 0 (by decide +kernel)
  | exact S 18 81 1 (by decide +kernel)
  | exact S 18 81 2 (by decide +kernel)
  | exact S 18 81 3 (by decide +kernel)
  | exact S 18 81 4 (by decide +kernel)
  | exact S 18 81 5 (by decide +kernel)
theorem q18_82:ThresholdAt 18 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 82 0 (by decide +kernel)
  | exact S 18 82 1 (by decide +kernel)
  | exact S 18 82 2 (by decide +kernel)
  | exact S 18 82 3 (by decide +kernel)
  | exact S 18 82 4 (by decide +kernel)
  | exact S 18 82 5 (by decide +kernel)
theorem q18_83:ThresholdAt 18 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 83 0 (by decide +kernel)
  | exact S 18 83 1 (by decide +kernel)
  | exact S 18 83 2 (by decide +kernel)
  | exact S 18 83 3 (by decide +kernel)
  | exact S 18 83 4 (by decide +kernel)
  | exact S 18 83 5 (by decide +kernel)
theorem q18_84:ThresholdAt 18 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 84 0 (by decide +kernel)
  | exact S 18 84 1 (by decide +kernel)
  | exact S 18 84 2 (by decide +kernel)
  | exact S 18 84 3 (by decide +kernel)
  | exact S 18 84 4 (by decide +kernel)
  | exact S 18 84 5 (by decide +kernel)
theorem q18_85:ThresholdAt 18 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 85 0 (by decide +kernel)
  | exact S 18 85 1 (by decide +kernel)
  | exact S 18 85 2 (by decide +kernel)
  | exact S 18 85 3 (by decide +kernel)
  | exact S 18 85 4 (by decide +kernel)
  | exact S 18 85 5 (by decide +kernel)
theorem q18_86:ThresholdAt 18 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 86 0 (by decide +kernel)
  | exact S 18 86 1 (by decide +kernel)
  | exact S 18 86 2 (by decide +kernel)
  | exact S 18 86 3 (by decide +kernel)
  | exact S 18 86 4 (by decide +kernel)
  | exact S 18 86 5 (by decide +kernel)
theorem q18_87:ThresholdAt 18 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 87 0 (by decide +kernel)
  | exact S 18 87 1 (by decide +kernel)
  | exact S 18 87 2 (by decide +kernel)
  | exact S 18 87 3 (by decide +kernel)
  | exact S 18 87 4 (by decide +kernel)
  | exact S 18 87 5 (by decide +kernel)
theorem q18_88:ThresholdAt 18 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 88 0 (by decide +kernel)
  | exact S 18 88 1 (by decide +kernel)
  | exact S 18 88 2 (by decide +kernel)
  | exact S 18 88 3 (by decide +kernel)
  | exact S 18 88 4 (by decide +kernel)
  | exact S 18 88 5 (by decide +kernel)
theorem q18_89:ThresholdAt 18 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 89 0 (by decide +kernel)
  | exact S 18 89 1 (by decide +kernel)
  | exact S 18 89 2 (by decide +kernel)
  | exact S 18 89 3 (by decide +kernel)
  | exact S 18 89 4 (by decide +kernel)
  | exact S 18 89 5 (by decide +kernel)
theorem q18_90:ThresholdAt 18 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 90 0 (by decide +kernel)
  | exact S 18 90 1 (by decide +kernel)
  | exact S 18 90 2 (by decide +kernel)
  | exact S 18 90 3 (by decide +kernel)
  | exact S 18 90 4 (by decide +kernel)
  | exact S 18 90 5 (by decide +kernel)
theorem q18_91:ThresholdAt 18 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 91 0 (by decide +kernel)
  | exact S 18 91 1 (by decide +kernel)
  | exact S 18 91 2 (by decide +kernel)
  | exact S 18 91 3 (by decide +kernel)
  | exact S 18 91 4 (by decide +kernel)
  | exact S 18 91 5 (by decide +kernel)
theorem q18_92:ThresholdAt 18 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 92 0 (by decide +kernel)
  | exact S 18 92 1 (by decide +kernel)
  | exact S 18 92 2 (by decide +kernel)
  | exact S 18 92 3 (by decide +kernel)
  | exact S 18 92 4 (by decide +kernel)
  | exact S 18 92 5 (by decide +kernel)
theorem q18_93:ThresholdAt 18 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 93 0 (by decide +kernel)
  | exact S 18 93 1 (by decide +kernel)
  | exact S 18 93 2 (by decide +kernel)
  | exact S 18 93 3 (by decide +kernel)
  | exact S 18 93 4 (by decide +kernel)
  | exact S 18 93 5 (by decide +kernel)
theorem q18_94:ThresholdAt 18 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 94 0 (by decide +kernel)
  | exact S 18 94 1 (by decide +kernel)
  | exact S 18 94 2 (by decide +kernel)
  | exact S 18 94 3 (by decide +kernel)
  | exact S 18 94 4 (by decide +kernel)
  | exact S 18 94 5 (by decide +kernel)
theorem q18_95:ThresholdAt 18 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 95 0 (by decide +kernel)
  | exact S 18 95 1 (by decide +kernel)
  | exact S 18 95 2 (by decide +kernel)
  | exact S 18 95 3 (by decide +kernel)
  | exact S 18 95 4 (by decide +kernel)
  | exact S 18 95 5 (by decide +kernel)
theorem q18_96:ThresholdAt 18 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 96 0 (by decide +kernel)
  | exact S 18 96 1 (by decide +kernel)
  | exact S 18 96 2 (by decide +kernel)
  | exact S 18 96 3 (by decide +kernel)
  | exact S 18 96 4 (by decide +kernel)
  | exact S 18 96 5 (by decide +kernel)
theorem q18_97:ThresholdAt 18 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 97 0 (by decide +kernel)
  | exact S 18 97 1 (by decide +kernel)
  | exact S 18 97 2 (by decide +kernel)
  | exact S 18 97 3 (by decide +kernel)
  | exact S 18 97 4 (by decide +kernel)
  | exact S 18 97 5 (by decide +kernel)
theorem q18_98:ThresholdAt 18 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 98 0 (by decide +kernel)
  | exact S 18 98 1 (by decide +kernel)
  | exact S 18 98 2 (by decide +kernel)
  | exact S 18 98 3 (by decide +kernel)
  | exact S 18 98 4 (by decide +kernel)
  | exact S 18 98 5 (by decide +kernel)
theorem q18_99:ThresholdAt 18 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 99 0 (by decide +kernel)
  | exact S 18 99 1 (by decide +kernel)
  | exact S 18 99 2 (by decide +kernel)
  | exact S 18 99 3 (by decide +kernel)
  | exact S 18 99 4 (by decide +kernel)
  | exact S 18 99 5 (by decide +kernel)
theorem q18_100:ThresholdAt 18 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 100 0 (by decide +kernel)
  | exact S 18 100 1 (by decide +kernel)
  | exact S 18 100 2 (by decide +kernel)
  | exact S 18 100 3 (by decide +kernel)
  | exact S 18 100 4 (by decide +kernel)
  | exact S 18 100 5 (by decide +kernel)
theorem q18_101:ThresholdAt 18 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 101 0 (by decide +kernel)
  | exact S 18 101 1 (by decide +kernel)
  | exact S 18 101 2 (by decide +kernel)
  | exact S 18 101 3 (by decide +kernel)
  | exact S 18 101 4 (by decide +kernel)
  | exact S 18 101 5 (by decide +kernel)
theorem q18_102:ThresholdAt 18 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 102 0 (by decide +kernel)
  | exact S 18 102 1 (by decide +kernel)
  | exact S 18 102 2 (by decide +kernel)
  | exact S 18 102 3 (by decide +kernel)
  | exact S 18 102 4 (by decide +kernel)
  | exact S 18 102 5 (by decide +kernel)
theorem q18_103:ThresholdAt 18 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 103 0 (by decide +kernel)
  | exact S 18 103 1 (by decide +kernel)
  | exact S 18 103 2 (by decide +kernel)
  | exact S 18 103 3 (by decide +kernel)
  | exact S 18 103 4 (by decide +kernel)
  | exact S 18 103 5 (by decide +kernel)
theorem q18_104:ThresholdAt 18 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 104 0 (by decide +kernel)
  | exact S 18 104 1 (by decide +kernel)
  | exact S 18 104 2 (by decide +kernel)
  | exact S 18 104 3 (by decide +kernel)
  | exact S 18 104 4 (by decide +kernel)
  | exact S 18 104 5 (by decide +kernel)
theorem q18_105:ThresholdAt 18 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 105 0 (by decide +kernel)
  | exact S 18 105 1 (by decide +kernel)
  | exact S 18 105 2 (by decide +kernel)
  | exact S 18 105 3 (by decide +kernel)
  | exact S 18 105 4 (by decide +kernel)
  | exact S 18 105 5 (by decide +kernel)
theorem q18_106:ThresholdAt 18 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 106 0 (by decide +kernel)
  | exact S 18 106 1 (by decide +kernel)
  | exact S 18 106 2 (by decide +kernel)
  | exact S 18 106 3 (by decide +kernel)
  | exact S 18 106 4 (by decide +kernel)
  | exact S 18 106 5 (by decide +kernel)
theorem q18_107:ThresholdAt 18 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 107 0 (by decide +kernel)
  | exact S 18 107 1 (by decide +kernel)
  | exact S 18 107 2 (by decide +kernel)
  | exact S 18 107 3 (by decide +kernel)
  | exact S 18 107 4 (by decide +kernel)
  | exact S 18 107 5 (by decide +kernel)
theorem q18_108:ThresholdAt 18 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 108 0 (by decide +kernel)
  | exact S 18 108 1 (by decide +kernel)
  | exact S 18 108 2 (by decide +kernel)
  | exact S 18 108 3 (by decide +kernel)
  | exact S 18 108 4 (by decide +kernel)
  | exact S 18 108 5 (by decide +kernel)
theorem q18_109:ThresholdAt 18 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 109 0 (by decide +kernel)
  | exact S 18 109 1 (by decide +kernel)
  | exact S 18 109 2 (by decide +kernel)
  | exact S 18 109 3 (by decide +kernel)
  | exact S 18 109 4 (by decide +kernel)
  | exact S 18 109 5 (by decide +kernel)
theorem q18_110:ThresholdAt 18 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 110 0 (by decide +kernel)
  | exact S 18 110 1 (by decide +kernel)
  | exact S 18 110 2 (by decide +kernel)
  | exact S 18 110 3 (by decide +kernel)
  | exact S 18 110 4 (by decide +kernel)
  | exact S 18 110 5 (by decide +kernel)
theorem q18_111:ThresholdAt 18 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 111 0 (by decide +kernel)
  | exact S 18 111 1 (by decide +kernel)
  | exact S 18 111 2 (by decide +kernel)
  | exact S 18 111 3 (by decide +kernel)
  | exact S 18 111 4 (by decide +kernel)
  | exact S 18 111 5 (by decide +kernel)
theorem q18_112:ThresholdAt 18 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 112 0 (by decide +kernel)
  | exact S 18 112 1 (by decide +kernel)
  | exact S 18 112 2 (by decide +kernel)
  | exact S 18 112 3 (by decide +kernel)
  | exact S 18 112 4 (by decide +kernel)
  | exact S 18 112 5 (by decide +kernel)
theorem q18_113:ThresholdAt 18 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 113 0 (by decide +kernel)
  | exact S 18 113 1 (by decide +kernel)
  | exact S 18 113 2 (by decide +kernel)
  | exact S 18 113 3 (by decide +kernel)
  | exact S 18 113 4 (by decide +kernel)
  | exact S 18 113 5 (by decide +kernel)
theorem q18_114:ThresholdAt 18 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 114 0 (by decide +kernel)
  | exact S 18 114 1 (by decide +kernel)
  | exact S 18 114 2 (by decide +kernel)
  | exact S 18 114 3 (by decide +kernel)
  | exact S 18 114 4 (by decide +kernel)
  | exact S 18 114 5 (by decide +kernel)
theorem q18_115:ThresholdAt 18 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 115 0 (by decide +kernel)
  | exact S 18 115 1 (by decide +kernel)
  | exact S 18 115 2 (by decide +kernel)
  | exact S 18 115 3 (by decide +kernel)
  | exact S 18 115 4 (by decide +kernel)
  | exact S 18 115 5 (by decide +kernel)
theorem q18_116:ThresholdAt 18 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 116 0 (by decide +kernel)
  | exact S 18 116 1 (by decide +kernel)
  | exact S 18 116 2 (by decide +kernel)
  | exact S 18 116 3 (by decide +kernel)
  | exact S 18 116 4 (by decide +kernel)
  | exact S 18 116 5 (by decide +kernel)
theorem q18_117:ThresholdAt 18 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 117 0 (by decide +kernel)
  | exact S 18 117 1 (by decide +kernel)
  | exact S 18 117 2 (by decide +kernel)
  | exact S 18 117 3 (by decide +kernel)
  | exact S 18 117 4 (by decide +kernel)
  | exact S 18 117 5 (by decide +kernel)
theorem q18_118:ThresholdAt 18 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 118 0 (by decide +kernel)
  | exact S 18 118 1 (by decide +kernel)
  | exact S 18 118 2 (by decide +kernel)
  | exact S 18 118 3 (by decide +kernel)
  | exact S 18 118 4 (by decide +kernel)
  | exact S 18 118 5 (by decide +kernel)
theorem q18_119:ThresholdAt 18 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 119 0 (by decide +kernel)
  | exact S 18 119 1 (by decide +kernel)
  | exact S 18 119 2 (by decide +kernel)
  | exact S 18 119 3 (by decide +kernel)
  | exact S 18 119 4 (by decide +kernel)
  | exact S 18 119 5 (by decide +kernel)
theorem q18_120:ThresholdAt 18 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 120 0 (by decide +kernel)
  | exact S 18 120 1 (by decide +kernel)
  | exact S 18 120 2 (by decide +kernel)
  | exact S 18 120 3 (by decide +kernel)
  | exact S 18 120 4 (by decide +kernel)
  | exact S 18 120 5 (by decide +kernel)
theorem q18_121:ThresholdAt 18 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 121 0 (by decide +kernel)
  | exact S 18 121 1 (by decide +kernel)
  | exact S 18 121 2 (by decide +kernel)
  | exact S 18 121 3 (by decide +kernel)
  | exact S 18 121 4 (by decide +kernel)
  | exact S 18 121 5 (by decide +kernel)
theorem q18_122:ThresholdAt 18 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 122 0 (by decide +kernel)
  | exact S 18 122 1 (by decide +kernel)
  | exact S 18 122 2 (by decide +kernel)
  | exact S 18 122 3 (by decide +kernel)
  | exact S 18 122 4 (by decide +kernel)
  | exact S 18 122 5 (by decide +kernel)
theorem q18_123:ThresholdAt 18 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 123 0 (by decide +kernel)
  | exact S 18 123 1 (by decide +kernel)
  | exact S 18 123 2 (by decide +kernel)
  | exact S 18 123 3 (by decide +kernel)
  | exact S 18 123 4 (by decide +kernel)
  | exact S 18 123 5 (by decide +kernel)
theorem q18_124:ThresholdAt 18 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 18 124 0 (by decide +kernel)
  | exact S 18 124 1 (by decide +kernel)
  | exact S 18 124 2 (by decide +kernel)
  | exact S 18 124 3 (by decide +kernel)
  | exact S 18 124 4 (by decide +kernel)
  | exact S 18 124 5 (by decide +kernel)
theorem checkedR18:∀ V ∈ List.range 125,ThresholdAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0_125:V < 62
  · by_cases h0_62:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q18_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q18_1
              · have he:V = 2:=by omega
                subst V
                exact q18_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q18_3
              · have he:V = 4:=by omega
                subst V
                exact q18_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q18_5
              · have he:V = 6:=by omega
                subst V
                exact q18_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q18_7
              · have he:V = 8:=by omega
                subst V
                exact q18_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q18_9
              · have he:V = 10:=by omega
                subst V
                exact q18_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q18_11
              · have he:V = 12:=by omega
                subst V
                exact q18_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q18_13
              · have he:V = 14:=by omega
                subst V
                exact q18_14
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q18_15
              · have he:V = 16:=by omega
                subst V
                exact q18_16
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q18_17
              · have he:V = 18:=by omega
                subst V
                exact q18_18
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q18_19
              · have he:V = 20:=by omega
                subst V
                exact q18_20
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q18_21
              · have he:V = 22:=by omega
                subst V
                exact q18_22
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q18_23
              · have he:V = 24:=by omega
                subst V
                exact q18_24
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q18_25
              · have he:V = 26:=by omega
                subst V
                exact q18_26
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q18_27
              · have he:V = 28:=by omega
                subst V
                exact q18_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q18_29
              · have he:V = 30:=by omega
                subst V
                exact q18_30
    · by_cases h31_62:V < 46
      · by_cases h31_46:V < 38
        · by_cases h31_38:V < 34
          · by_cases h31_34:V < 32
            · have he:V = 31:=by omega
              subst V
              exact q18_31
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q18_32
              · have he:V = 33:=by omega
                subst V
                exact q18_33
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q18_34
              · have he:V = 35:=by omega
                subst V
                exact q18_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q18_36
              · have he:V = 37:=by omega
                subst V
                exact q18_37
        · by_cases h38_46:V < 42
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q18_38
              · have he:V = 39:=by omega
                subst V
                exact q18_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q18_40
              · have he:V = 41:=by omega
                subst V
                exact q18_41
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q18_42
              · have he:V = 43:=by omega
                subst V
                exact q18_43
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q18_44
              · have he:V = 45:=by omega
                subst V
                exact q18_45
      · by_cases h46_62:V < 54
        · by_cases h46_54:V < 50
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q18_46
              · have he:V = 47:=by omega
                subst V
                exact q18_47
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q18_48
              · have he:V = 49:=by omega
                subst V
                exact q18_49
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q18_50
              · have he:V = 51:=by omega
                subst V
                exact q18_51
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q18_52
              · have he:V = 53:=by omega
                subst V
                exact q18_53
        · by_cases h54_62:V < 58
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q18_54
              · have he:V = 55:=by omega
                subst V
                exact q18_55
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q18_56
              · have he:V = 57:=by omega
                subst V
                exact q18_57
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q18_58
              · have he:V = 59:=by omega
                subst V
                exact q18_59
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q18_60
              · have he:V = 61:=by omega
                subst V
                exact q18_61
  · by_cases h62_125:V < 93
    · by_cases h62_93:V < 77
      · by_cases h62_77:V < 69
        · by_cases h62_69:V < 65
          · by_cases h62_65:V < 63
            · have he:V = 62:=by omega
              subst V
              exact q18_62
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q18_63
              · have he:V = 64:=by omega
                subst V
                exact q18_64
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q18_65
              · have he:V = 66:=by omega
                subst V
                exact q18_66
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q18_67
              · have he:V = 68:=by omega
                subst V
                exact q18_68
        · by_cases h69_77:V < 73
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q18_69
              · have he:V = 70:=by omega
                subst V
                exact q18_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q18_71
              · have he:V = 72:=by omega
                subst V
                exact q18_72
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q18_73
              · have he:V = 74:=by omega
                subst V
                exact q18_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q18_75
              · have he:V = 76:=by omega
                subst V
                exact q18_76
      · by_cases h77_93:V < 85
        · by_cases h77_85:V < 81
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q18_77
              · have he:V = 78:=by omega
                subst V
                exact q18_78
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q18_79
              · have he:V = 80:=by omega
                subst V
                exact q18_80
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q18_81
              · have he:V = 82:=by omega
                subst V
                exact q18_82
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q18_83
              · have he:V = 84:=by omega
                subst V
                exact q18_84
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q18_85
              · have he:V = 86:=by omega
                subst V
                exact q18_86
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q18_87
              · have he:V = 88:=by omega
                subst V
                exact q18_88
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q18_89
              · have he:V = 90:=by omega
                subst V
                exact q18_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q18_91
              · have he:V = 92:=by omega
                subst V
                exact q18_92
    · by_cases h93_125:V < 109
      · by_cases h93_109:V < 101
        · by_cases h93_101:V < 97
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q18_93
              · have he:V = 94:=by omega
                subst V
                exact q18_94
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q18_95
              · have he:V = 96:=by omega
                subst V
                exact q18_96
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q18_97
              · have he:V = 98:=by omega
                subst V
                exact q18_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q18_99
              · have he:V = 100:=by omega
                subst V
                exact q18_100
        · by_cases h101_109:V < 105
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q18_101
              · have he:V = 102:=by omega
                subst V
                exact q18_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q18_103
              · have he:V = 104:=by omega
                subst V
                exact q18_104
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q18_105
              · have he:V = 106:=by omega
                subst V
                exact q18_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q18_107
              · have he:V = 108:=by omega
                subst V
                exact q18_108
      · by_cases h109_125:V < 117
        · by_cases h109_117:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q18_109
              · have he:V = 110:=by omega
                subst V
                exact q18_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q18_111
              · have he:V = 112:=by omega
                subst V
                exact q18_112
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q18_113
              · have he:V = 114:=by omega
                subst V
                exact q18_114
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q18_115
              · have he:V = 116:=by omega
                subst V
                exact q18_116
        · by_cases h117_125:V < 121
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q18_117
              · have he:V = 118:=by omega
                subst V
                exact q18_118
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q18_119
              · have he:V = 120:=by omega
                subst V
                exact q18_120
          · by_cases h121_125:V < 123
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q18_121
              · have he:V = 122:=by omega
                subst V
                exact q18_122
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q18_123
              · have he:V = 124:=by omega
                subst V
                exact q18_124
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
