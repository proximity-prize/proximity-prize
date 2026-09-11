import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked13

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q14_0:ThresholdAt 14 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 0 0 (by decide +kernel)
  | exact S 14 0 1 (by decide +kernel)
  | exact S 14 0 2 (by decide +kernel)
  | exact S 14 0 3 (by decide +kernel)
  | exact S 14 0 4 (by decide +kernel)
  | exact S 14 0 5 (by decide +kernel)
theorem q14_1:ThresholdAt 14 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 1 0 (by decide +kernel)
  | exact S 14 1 1 (by decide +kernel)
  | exact S 14 1 2 (by decide +kernel)
  | exact S 14 1 3 (by decide +kernel)
  | exact S 14 1 4 (by decide +kernel)
  | exact S 14 1 5 (by decide +kernel)
theorem q14_2:ThresholdAt 14 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 2 0 (by decide +kernel)
  | exact S 14 2 1 (by decide +kernel)
  | exact S 14 2 2 (by decide +kernel)
  | exact S 14 2 3 (by decide +kernel)
  | exact S 14 2 4 (by decide +kernel)
  | exact S 14 2 5 (by decide +kernel)
theorem q14_3:ThresholdAt 14 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 3 0 (by decide +kernel)
  | exact S 14 3 1 (by decide +kernel)
  | exact S 14 3 2 (by decide +kernel)
  | exact S 14 3 3 (by decide +kernel)
  | exact S 14 3 4 (by decide +kernel)
  | exact S 14 3 5 (by decide +kernel)
theorem q14_4:ThresholdAt 14 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 4 0 (by decide +kernel)
  | exact S 14 4 1 (by decide +kernel)
  | exact S 14 4 2 (by decide +kernel)
  | exact S 14 4 3 (by decide +kernel)
  | exact S 14 4 4 (by decide +kernel)
  | exact S 14 4 5 (by decide +kernel)
theorem q14_5:ThresholdAt 14 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 5 0 (by decide +kernel)
  | exact S 14 5 1 (by decide +kernel)
  | exact S 14 5 2 (by decide +kernel)
  | exact S 14 5 3 (by decide +kernel)
  | exact S 14 5 4 (by decide +kernel)
  | exact S 14 5 5 (by decide +kernel)
theorem q14_6:ThresholdAt 14 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 6 0 (by decide +kernel)
  | exact S 14 6 1 (by decide +kernel)
  | exact S 14 6 2 (by decide +kernel)
  | exact S 14 6 3 (by decide +kernel)
  | exact S 14 6 4 (by decide +kernel)
  | exact S 14 6 5 (by decide +kernel)
theorem q14_7:ThresholdAt 14 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 7 0 (by decide +kernel)
  | exact S 14 7 1 (by decide +kernel)
  | exact S 14 7 2 (by decide +kernel)
  | exact S 14 7 3 (by decide +kernel)
  | exact S 14 7 4 (by decide +kernel)
  | exact S 14 7 5 (by decide +kernel)
theorem q14_8:ThresholdAt 14 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 8 0 (by decide +kernel)
  | exact S 14 8 1 (by decide +kernel)
  | exact S 14 8 2 (by decide +kernel)
  | exact S 14 8 3 (by decide +kernel)
  | exact S 14 8 4 (by decide +kernel)
  | exact S 14 8 5 (by decide +kernel)
theorem q14_9:ThresholdAt 14 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 9 0 (by decide +kernel)
  | exact S 14 9 1 (by decide +kernel)
  | exact S 14 9 2 (by decide +kernel)
  | exact S 14 9 3 (by decide +kernel)
  | exact S 14 9 4 (by decide +kernel)
  | exact S 14 9 5 (by decide +kernel)
theorem q14_10:ThresholdAt 14 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 10 0 (by decide +kernel)
  | exact S 14 10 1 (by decide +kernel)
  | exact S 14 10 2 (by decide +kernel)
  | exact S 14 10 3 (by decide +kernel)
  | exact S 14 10 4 (by decide +kernel)
  | exact S 14 10 5 (by decide +kernel)
theorem q14_11:ThresholdAt 14 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 11 0 (by decide +kernel)
  | exact S 14 11 1 (by decide +kernel)
  | exact S 14 11 2 (by decide +kernel)
  | exact S 14 11 3 (by decide +kernel)
  | exact S 14 11 4 (by decide +kernel)
  | exact S 14 11 5 (by decide +kernel)
theorem q14_12:ThresholdAt 14 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 12 0 (by decide +kernel)
  | exact S 14 12 1 (by decide +kernel)
  | exact S 14 12 2 (by decide +kernel)
  | exact S 14 12 3 (by decide +kernel)
  | exact S 14 12 4 (by decide +kernel)
  | exact S 14 12 5 (by decide +kernel)
theorem q14_13:ThresholdAt 14 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 13 0 (by decide +kernel)
  | exact S 14 13 1 (by decide +kernel)
  | exact S 14 13 2 (by decide +kernel)
  | exact S 14 13 3 (by decide +kernel)
  | exact S 14 13 4 (by decide +kernel)
  | exact S 14 13 5 (by decide +kernel)
theorem q14_14:ThresholdAt 14 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 14 0 (by decide +kernel)
  | exact S 14 14 1 (by decide +kernel)
  | exact S 14 14 2 (by decide +kernel)
  | exact S 14 14 3 (by decide +kernel)
  | exact S 14 14 4 (by decide +kernel)
  | exact S 14 14 5 (by decide +kernel)
theorem q14_15:ThresholdAt 14 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 15 0 (by decide +kernel)
  | exact S 14 15 1 (by decide +kernel)
  | exact S 14 15 2 (by decide +kernel)
  | exact S 14 15 3 (by decide +kernel)
  | exact S 14 15 4 (by decide +kernel)
  | exact S 14 15 5 (by decide +kernel)
theorem q14_16:ThresholdAt 14 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 16 0 (by decide +kernel)
  | exact S 14 16 1 (by decide +kernel)
  | exact S 14 16 2 (by decide +kernel)
  | exact S 14 16 3 (by decide +kernel)
  | exact S 14 16 4 (by decide +kernel)
  | exact S 14 16 5 (by decide +kernel)
theorem q14_17:ThresholdAt 14 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 17 0 (by decide +kernel)
  | exact S 14 17 1 (by decide +kernel)
  | exact S 14 17 2 (by decide +kernel)
  | exact S 14 17 3 (by decide +kernel)
  | exact S 14 17 4 (by decide +kernel)
  | exact S 14 17 5 (by decide +kernel)
theorem q14_18:ThresholdAt 14 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 18 0 (by decide +kernel)
  | exact S 14 18 1 (by decide +kernel)
  | exact S 14 18 2 (by decide +kernel)
  | exact S 14 18 3 (by decide +kernel)
  | exact S 14 18 4 (by decide +kernel)
  | exact S 14 18 5 (by decide +kernel)
theorem q14_19:ThresholdAt 14 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 19 0 (by decide +kernel)
  | exact S 14 19 1 (by decide +kernel)
  | exact S 14 19 2 (by decide +kernel)
  | exact S 14 19 3 (by decide +kernel)
  | exact S 14 19 4 (by decide +kernel)
  | exact S 14 19 5 (by decide +kernel)
theorem q14_20:ThresholdAt 14 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 20 0 (by decide +kernel)
  | exact S 14 20 1 (by decide +kernel)
  | exact S 14 20 2 (by decide +kernel)
  | exact S 14 20 3 (by decide +kernel)
  | exact S 14 20 4 (by decide +kernel)
  | exact S 14 20 5 (by decide +kernel)
theorem q14_21:ThresholdAt 14 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 21 0 (by decide +kernel)
  | exact S 14 21 1 (by decide +kernel)
  | exact S 14 21 2 (by decide +kernel)
  | exact S 14 21 3 (by decide +kernel)
  | exact S 14 21 4 (by decide +kernel)
  | exact S 14 21 5 (by decide +kernel)
theorem q14_22:ThresholdAt 14 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 22 0 (by decide +kernel)
  | exact S 14 22 1 (by decide +kernel)
  | exact S 14 22 2 (by decide +kernel)
  | exact S 14 22 3 (by decide +kernel)
  | exact S 14 22 4 (by decide +kernel)
  | exact S 14 22 5 (by decide +kernel)
theorem q14_23:ThresholdAt 14 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 23 0 (by decide +kernel)
  | exact S 14 23 1 (by decide +kernel)
  | exact S 14 23 2 (by decide +kernel)
  | exact S 14 23 3 (by decide +kernel)
  | exact S 14 23 4 (by decide +kernel)
  | exact S 14 23 5 (by decide +kernel)
theorem q14_24:ThresholdAt 14 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 24 0 (by decide +kernel)
  | exact S 14 24 1 (by decide +kernel)
  | exact S 14 24 2 (by decide +kernel)
  | exact S 14 24 3 (by decide +kernel)
  | exact S 14 24 4 (by decide +kernel)
  | exact S 14 24 5 (by decide +kernel)
theorem q14_25:ThresholdAt 14 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 25 0 (by decide +kernel)
  | exact S 14 25 1 (by decide +kernel)
  | exact S 14 25 2 (by decide +kernel)
  | exact S 14 25 3 (by decide +kernel)
  | exact S 14 25 4 (by decide +kernel)
  | exact S 14 25 5 (by decide +kernel)
theorem q14_26:ThresholdAt 14 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 26 0 (by decide +kernel)
  | exact S 14 26 1 (by decide +kernel)
  | exact S 14 26 2 (by decide +kernel)
  | exact S 14 26 3 (by decide +kernel)
  | exact S 14 26 4 (by decide +kernel)
  | exact S 14 26 5 (by decide +kernel)
theorem q14_27:ThresholdAt 14 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 27 0 (by decide +kernel)
  | exact S 14 27 1 (by decide +kernel)
  | exact S 14 27 2 (by decide +kernel)
  | exact S 14 27 3 (by decide +kernel)
  | exact S 14 27 4 (by decide +kernel)
  | exact S 14 27 5 (by decide +kernel)
theorem q14_28:ThresholdAt 14 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 28 0 (by decide +kernel)
  | exact S 14 28 1 (by decide +kernel)
  | exact S 14 28 2 (by decide +kernel)
  | exact S 14 28 3 (by decide +kernel)
  | exact S 14 28 4 (by decide +kernel)
  | exact S 14 28 5 (by decide +kernel)
theorem q14_29:ThresholdAt 14 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 29 0 (by decide +kernel)
  | exact S 14 29 1 (by decide +kernel)
  | exact S 14 29 2 (by decide +kernel)
  | exact S 14 29 3 (by decide +kernel)
  | exact S 14 29 4 (by decide +kernel)
  | exact S 14 29 5 (by decide +kernel)
theorem q14_30:ThresholdAt 14 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 30 0 (by decide +kernel)
  | exact S 14 30 1 (by decide +kernel)
  | exact S 14 30 2 (by decide +kernel)
  | exact S 14 30 3 (by decide +kernel)
  | exact S 14 30 4 (by decide +kernel)
  | exact S 14 30 5 (by decide +kernel)
theorem q14_31:ThresholdAt 14 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 31 0 (by decide +kernel)
  | exact S 14 31 1 (by decide +kernel)
  | exact S 14 31 2 (by decide +kernel)
  | exact S 14 31 3 (by decide +kernel)
  | exact S 14 31 4 (by decide +kernel)
  | exact S 14 31 5 (by decide +kernel)
theorem q14_32:ThresholdAt 14 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 32 0 (by decide +kernel)
  | exact S 14 32 1 (by decide +kernel)
  | exact S 14 32 2 (by decide +kernel)
  | exact S 14 32 3 (by decide +kernel)
  | exact S 14 32 4 (by decide +kernel)
  | exact S 14 32 5 (by decide +kernel)
theorem q14_33:ThresholdAt 14 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 33 0 (by decide +kernel)
  | exact S 14 33 1 (by decide +kernel)
  | exact S 14 33 2 (by decide +kernel)
  | exact S 14 33 3 (by decide +kernel)
  | exact S 14 33 4 (by decide +kernel)
  | exact S 14 33 5 (by decide +kernel)
theorem q14_34:ThresholdAt 14 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 34 0 (by decide +kernel)
  | exact S 14 34 1 (by decide +kernel)
  | exact S 14 34 2 (by decide +kernel)
  | exact S 14 34 3 (by decide +kernel)
  | exact S 14 34 4 (by decide +kernel)
  | exact S 14 34 5 (by decide +kernel)
theorem q14_35:ThresholdAt 14 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 35 0 (by decide +kernel)
  | exact S 14 35 1 (by decide +kernel)
  | exact S 14 35 2 (by decide +kernel)
  | exact S 14 35 3 (by decide +kernel)
  | exact S 14 35 4 (by decide +kernel)
  | exact S 14 35 5 (by decide +kernel)
theorem q14_36:ThresholdAt 14 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 36 0 (by decide +kernel)
  | exact S 14 36 1 (by decide +kernel)
  | exact S 14 36 2 (by decide +kernel)
  | exact S 14 36 3 (by decide +kernel)
  | exact S 14 36 4 (by decide +kernel)
  | exact S 14 36 5 (by decide +kernel)
theorem q14_37:ThresholdAt 14 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 37 0 (by decide +kernel)
  | exact S 14 37 1 (by decide +kernel)
  | exact S 14 37 2 (by decide +kernel)
  | exact S 14 37 3 (by decide +kernel)
  | exact S 14 37 4 (by decide +kernel)
  | exact S 14 37 5 (by decide +kernel)
theorem q14_38:ThresholdAt 14 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 38 0 (by decide +kernel)
  | exact S 14 38 1 (by decide +kernel)
  | exact S 14 38 2 (by decide +kernel)
  | exact S 14 38 3 (by decide +kernel)
  | exact S 14 38 4 (by decide +kernel)
  | exact S 14 38 5 (by decide +kernel)
theorem q14_39:ThresholdAt 14 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 39 0 (by decide +kernel)
  | exact S 14 39 1 (by decide +kernel)
  | exact S 14 39 2 (by decide +kernel)
  | exact S 14 39 3 (by decide +kernel)
  | exact S 14 39 4 (by decide +kernel)
  | exact S 14 39 5 (by decide +kernel)
theorem q14_40:ThresholdAt 14 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 40 0 (by decide +kernel)
  | exact S 14 40 1 (by decide +kernel)
  | exact S 14 40 2 (by decide +kernel)
  | exact S 14 40 3 (by decide +kernel)
  | exact S 14 40 4 (by decide +kernel)
  | exact S 14 40 5 (by decide +kernel)
theorem q14_41:ThresholdAt 14 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 41 0 (by decide +kernel)
  | exact S 14 41 1 (by decide +kernel)
  | exact S 14 41 2 (by decide +kernel)
  | exact S 14 41 3 (by decide +kernel)
  | exact S 14 41 4 (by decide +kernel)
  | exact S 14 41 5 (by decide +kernel)
theorem q14_42:ThresholdAt 14 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 42 0 (by decide +kernel)
  | exact S 14 42 1 (by decide +kernel)
  | exact S 14 42 2 (by decide +kernel)
  | exact S 14 42 3 (by decide +kernel)
  | exact S 14 42 4 (by decide +kernel)
  | exact S 14 42 5 (by decide +kernel)
theorem q14_43:ThresholdAt 14 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 43 0 (by decide +kernel)
  | exact S 14 43 1 (by decide +kernel)
  | exact S 14 43 2 (by decide +kernel)
  | exact S 14 43 3 (by decide +kernel)
  | exact S 14 43 4 (by decide +kernel)
  | exact S 14 43 5 (by decide +kernel)
theorem q14_44:ThresholdAt 14 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 44 0 (by decide +kernel)
  | exact S 14 44 1 (by decide +kernel)
  | exact S 14 44 2 (by decide +kernel)
  | exact S 14 44 3 (by decide +kernel)
  | exact S 14 44 4 (by decide +kernel)
  | exact S 14 44 5 (by decide +kernel)
theorem q14_45:ThresholdAt 14 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 45 0 (by decide +kernel)
  | exact S 14 45 1 (by decide +kernel)
  | exact S 14 45 2 (by decide +kernel)
  | exact S 14 45 3 (by decide +kernel)
  | exact S 14 45 4 (by decide +kernel)
  | exact S 14 45 5 (by decide +kernel)
theorem q14_46:ThresholdAt 14 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 46 0 (by decide +kernel)
  | exact S 14 46 1 (by decide +kernel)
  | exact S 14 46 2 (by decide +kernel)
  | exact S 14 46 3 (by decide +kernel)
  | exact S 14 46 4 (by decide +kernel)
  | exact S 14 46 5 (by decide +kernel)
theorem q14_47:ThresholdAt 14 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 47 0 (by decide +kernel)
  | exact S 14 47 1 (by decide +kernel)
  | exact S 14 47 2 (by decide +kernel)
  | exact S 14 47 3 (by decide +kernel)
  | exact S 14 47 4 (by decide +kernel)
  | exact S 14 47 5 (by decide +kernel)
theorem q14_48:ThresholdAt 14 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 48 0 (by decide +kernel)
  | exact S 14 48 1 (by decide +kernel)
  | exact S 14 48 2 (by decide +kernel)
  | exact S 14 48 3 (by decide +kernel)
  | exact S 14 48 4 (by decide +kernel)
  | exact S 14 48 5 (by decide +kernel)
theorem q14_49:ThresholdAt 14 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 49 0 (by decide +kernel)
  | exact S 14 49 1 (by decide +kernel)
  | exact S 14 49 2 (by decide +kernel)
  | exact S 14 49 3 (by decide +kernel)
  | exact S 14 49 4 (by decide +kernel)
  | exact S 14 49 5 (by decide +kernel)
theorem q14_50:ThresholdAt 14 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 50 0 (by decide +kernel)
  | exact S 14 50 1 (by decide +kernel)
  | exact S 14 50 2 (by decide +kernel)
  | exact S 14 50 3 (by decide +kernel)
  | exact S 14 50 4 (by decide +kernel)
  | exact S 14 50 5 (by decide +kernel)
theorem q14_51:ThresholdAt 14 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 51 0 (by decide +kernel)
  | exact S 14 51 1 (by decide +kernel)
  | exact S 14 51 2 (by decide +kernel)
  | exact S 14 51 3 (by decide +kernel)
  | exact S 14 51 4 (by decide +kernel)
  | exact S 14 51 5 (by decide +kernel)
theorem q14_52:ThresholdAt 14 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 52 0 (by decide +kernel)
  | exact S 14 52 1 (by decide +kernel)
  | exact S 14 52 2 (by decide +kernel)
  | exact S 14 52 3 (by decide +kernel)
  | exact S 14 52 4 (by decide +kernel)
  | exact S 14 52 5 (by decide +kernel)
theorem q14_53:ThresholdAt 14 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 53 0 (by decide +kernel)
  | exact S 14 53 1 (by decide +kernel)
  | exact S 14 53 2 (by decide +kernel)
  | exact S 14 53 3 (by decide +kernel)
  | exact S 14 53 4 (by decide +kernel)
  | exact S 14 53 5 (by decide +kernel)
theorem q14_54:ThresholdAt 14 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 54 0 (by decide +kernel)
  | exact S 14 54 1 (by decide +kernel)
  | exact S 14 54 2 (by decide +kernel)
  | exact S 14 54 3 (by decide +kernel)
  | exact S 14 54 4 (by decide +kernel)
  | exact S 14 54 5 (by decide +kernel)
theorem q14_55:ThresholdAt 14 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 55 0 (by decide +kernel)
  | exact S 14 55 1 (by decide +kernel)
  | exact S 14 55 2 (by decide +kernel)
  | exact S 14 55 3 (by decide +kernel)
  | exact S 14 55 4 (by decide +kernel)
  | exact S 14 55 5 (by decide +kernel)
theorem q14_56:ThresholdAt 14 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 56 0 (by decide +kernel)
  | exact S 14 56 1 (by decide +kernel)
  | exact S 14 56 2 (by decide +kernel)
  | exact S 14 56 3 (by decide +kernel)
  | exact S 14 56 4 (by decide +kernel)
  | exact S 14 56 5 (by decide +kernel)
theorem q14_57:ThresholdAt 14 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 57 0 (by decide +kernel)
  | exact S 14 57 1 (by decide +kernel)
  | exact S 14 57 2 (by decide +kernel)
  | exact S 14 57 3 (by decide +kernel)
  | exact S 14 57 4 (by decide +kernel)
  | exact S 14 57 5 (by decide +kernel)
theorem q14_58:ThresholdAt 14 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 58 0 (by decide +kernel)
  | exact S 14 58 1 (by decide +kernel)
  | exact S 14 58 2 (by decide +kernel)
  | exact S 14 58 3 (by decide +kernel)
  | exact S 14 58 4 (by decide +kernel)
  | exact S 14 58 5 (by decide +kernel)
theorem q14_59:ThresholdAt 14 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 59 0 (by decide +kernel)
  | exact S 14 59 1 (by decide +kernel)
  | exact S 14 59 2 (by decide +kernel)
  | exact S 14 59 3 (by decide +kernel)
  | exact S 14 59 4 (by decide +kernel)
  | exact S 14 59 5 (by decide +kernel)
theorem q14_60:ThresholdAt 14 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 60 0 (by decide +kernel)
  | exact S 14 60 1 (by decide +kernel)
  | exact S 14 60 2 (by decide +kernel)
  | exact S 14 60 3 (by decide +kernel)
  | exact S 14 60 4 (by decide +kernel)
  | exact S 14 60 5 (by decide +kernel)
theorem q14_61:ThresholdAt 14 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 61 0 (by decide +kernel)
  | exact S 14 61 1 (by decide +kernel)
  | exact S 14 61 2 (by decide +kernel)
  | exact S 14 61 3 (by decide +kernel)
  | exact S 14 61 4 (by decide +kernel)
  | exact S 14 61 5 (by decide +kernel)
theorem q14_62:ThresholdAt 14 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 62 0 (by decide +kernel)
  | exact S 14 62 1 (by decide +kernel)
  | exact S 14 62 2 (by decide +kernel)
  | exact S 14 62 3 (by decide +kernel)
  | exact S 14 62 4 (by decide +kernel)
  | exact S 14 62 5 (by decide +kernel)
theorem q14_63:ThresholdAt 14 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 63 0 (by decide +kernel)
  | exact S 14 63 1 (by decide +kernel)
  | exact S 14 63 2 (by decide +kernel)
  | exact S 14 63 3 (by decide +kernel)
  | exact S 14 63 4 (by decide +kernel)
  | exact S 14 63 5 (by decide +kernel)
theorem q14_64:ThresholdAt 14 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 64 0 (by decide +kernel)
  | exact S 14 64 1 (by decide +kernel)
  | exact S 14 64 2 (by decide +kernel)
  | exact S 14 64 3 (by decide +kernel)
  | exact S 14 64 4 (by decide +kernel)
  | exact S 14 64 5 (by decide +kernel)
theorem q14_65:ThresholdAt 14 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 65 0 (by decide +kernel)
  | exact S 14 65 1 (by decide +kernel)
  | exact S 14 65 2 (by decide +kernel)
  | exact S 14 65 3 (by decide +kernel)
  | exact S 14 65 4 (by decide +kernel)
  | exact S 14 65 5 (by decide +kernel)
theorem q14_66:ThresholdAt 14 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 66 0 (by decide +kernel)
  | exact S 14 66 1 (by decide +kernel)
  | exact S 14 66 2 (by decide +kernel)
  | exact S 14 66 3 (by decide +kernel)
  | exact S 14 66 4 (by decide +kernel)
  | exact S 14 66 5 (by decide +kernel)
theorem q14_67:ThresholdAt 14 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 67 0 (by decide +kernel)
  | exact S 14 67 1 (by decide +kernel)
  | exact S 14 67 2 (by decide +kernel)
  | exact S 14 67 3 (by decide +kernel)
  | exact S 14 67 4 (by decide +kernel)
  | exact S 14 67 5 (by decide +kernel)
theorem q14_68:ThresholdAt 14 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 68 0 (by decide +kernel)
  | exact S 14 68 1 (by decide +kernel)
  | exact S 14 68 2 (by decide +kernel)
  | exact S 14 68 3 (by decide +kernel)
  | exact S 14 68 4 (by decide +kernel)
  | exact S 14 68 5 (by decide +kernel)
theorem q14_69:ThresholdAt 14 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 69 0 (by decide +kernel)
  | exact S 14 69 1 (by decide +kernel)
  | exact S 14 69 2 (by decide +kernel)
  | exact S 14 69 3 (by decide +kernel)
  | exact S 14 69 4 (by decide +kernel)
  | exact S 14 69 5 (by decide +kernel)
theorem q14_70:ThresholdAt 14 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 70 0 (by decide +kernel)
  | exact S 14 70 1 (by decide +kernel)
  | exact S 14 70 2 (by decide +kernel)
  | exact S 14 70 3 (by decide +kernel)
  | exact S 14 70 4 (by decide +kernel)
  | exact S 14 70 5 (by decide +kernel)
theorem q14_71:ThresholdAt 14 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 71 0 (by decide +kernel)
  | exact S 14 71 1 (by decide +kernel)
  | exact S 14 71 2 (by decide +kernel)
  | exact S 14 71 3 (by decide +kernel)
  | exact S 14 71 4 (by decide +kernel)
  | exact S 14 71 5 (by decide +kernel)
theorem q14_72:ThresholdAt 14 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 72 0 (by decide +kernel)
  | exact S 14 72 1 (by decide +kernel)
  | exact S 14 72 2 (by decide +kernel)
  | exact S 14 72 3 (by decide +kernel)
  | exact S 14 72 4 (by decide +kernel)
  | exact S 14 72 5 (by decide +kernel)
theorem q14_73:ThresholdAt 14 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 73 0 (by decide +kernel)
  | exact S 14 73 1 (by decide +kernel)
  | exact S 14 73 2 (by decide +kernel)
  | exact S 14 73 3 (by decide +kernel)
  | exact S 14 73 4 (by decide +kernel)
  | exact S 14 73 5 (by decide +kernel)
theorem q14_74:ThresholdAt 14 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 74 0 (by decide +kernel)
  | exact S 14 74 1 (by decide +kernel)
  | exact S 14 74 2 (by decide +kernel)
  | exact S 14 74 3 (by decide +kernel)
  | exact S 14 74 4 (by decide +kernel)
  | exact S 14 74 5 (by decide +kernel)
theorem q14_75:ThresholdAt 14 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 75 0 (by decide +kernel)
  | exact S 14 75 1 (by decide +kernel)
  | exact S 14 75 2 (by decide +kernel)
  | exact S 14 75 3 (by decide +kernel)
  | exact S 14 75 4 (by decide +kernel)
  | exact S 14 75 5 (by decide +kernel)
theorem q14_76:ThresholdAt 14 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 76 0 (by decide +kernel)
  | exact S 14 76 1 (by decide +kernel)
  | exact S 14 76 2 (by decide +kernel)
  | exact S 14 76 3 (by decide +kernel)
  | exact S 14 76 4 (by decide +kernel)
  | exact S 14 76 5 (by decide +kernel)
theorem q14_77:ThresholdAt 14 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 77 0 (by decide +kernel)
  | exact S 14 77 1 (by decide +kernel)
  | exact S 14 77 2 (by decide +kernel)
  | exact S 14 77 3 (by decide +kernel)
  | exact S 14 77 4 (by decide +kernel)
  | exact S 14 77 5 (by decide +kernel)
theorem q14_78:ThresholdAt 14 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 78 0 (by decide +kernel)
  | exact S 14 78 1 (by decide +kernel)
  | exact S 14 78 2 (by decide +kernel)
  | exact S 14 78 3 (by decide +kernel)
  | exact S 14 78 4 (by decide +kernel)
  | exact S 14 78 5 (by decide +kernel)
theorem q14_79:ThresholdAt 14 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 79 0 (by decide +kernel)
  | exact S 14 79 1 (by decide +kernel)
  | exact S 14 79 2 (by decide +kernel)
  | exact S 14 79 3 (by decide +kernel)
  | exact S 14 79 4 (by decide +kernel)
  | exact S 14 79 5 (by decide +kernel)
theorem q14_80:ThresholdAt 14 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 80 0 (by decide +kernel)
  | exact S 14 80 1 (by decide +kernel)
  | exact S 14 80 2 (by decide +kernel)
  | exact S 14 80 3 (by decide +kernel)
  | exact S 14 80 4 (by decide +kernel)
  | exact S 14 80 5 (by decide +kernel)
theorem q14_81:ThresholdAt 14 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 81 0 (by decide +kernel)
  | exact S 14 81 1 (by decide +kernel)
  | exact S 14 81 2 (by decide +kernel)
  | exact S 14 81 3 (by decide +kernel)
  | exact S 14 81 4 (by decide +kernel)
  | exact S 14 81 5 (by decide +kernel)
theorem q14_82:ThresholdAt 14 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 82 0 (by decide +kernel)
  | exact S 14 82 1 (by decide +kernel)
  | exact S 14 82 2 (by decide +kernel)
  | exact S 14 82 3 (by decide +kernel)
  | exact S 14 82 4 (by decide +kernel)
  | exact S 14 82 5 (by decide +kernel)
theorem q14_83:ThresholdAt 14 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 83 0 (by decide +kernel)
  | exact S 14 83 1 (by decide +kernel)
  | exact S 14 83 2 (by decide +kernel)
  | exact S 14 83 3 (by decide +kernel)
  | exact S 14 83 4 (by decide +kernel)
  | exact S 14 83 5 (by decide +kernel)
theorem q14_84:ThresholdAt 14 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 84 0 (by decide +kernel)
  | exact S 14 84 1 (by decide +kernel)
  | exact S 14 84 2 (by decide +kernel)
  | exact S 14 84 3 (by decide +kernel)
  | exact S 14 84 4 (by decide +kernel)
  | exact S 14 84 5 (by decide +kernel)
theorem q14_85:ThresholdAt 14 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 85 0 (by decide +kernel)
  | exact S 14 85 1 (by decide +kernel)
  | exact S 14 85 2 (by decide +kernel)
  | exact S 14 85 3 (by decide +kernel)
  | exact S 14 85 4 (by decide +kernel)
  | exact S 14 85 5 (by decide +kernel)
theorem q14_86:ThresholdAt 14 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 86 0 (by decide +kernel)
  | exact S 14 86 1 (by decide +kernel)
  | exact S 14 86 2 (by decide +kernel)
  | exact S 14 86 3 (by decide +kernel)
  | exact S 14 86 4 (by decide +kernel)
  | exact S 14 86 5 (by decide +kernel)
theorem q14_87:ThresholdAt 14 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 87 0 (by decide +kernel)
  | exact S 14 87 1 (by decide +kernel)
  | exact S 14 87 2 (by decide +kernel)
  | exact S 14 87 3 (by decide +kernel)
  | exact S 14 87 4 (by decide +kernel)
  | exact S 14 87 5 (by decide +kernel)
theorem q14_88:ThresholdAt 14 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 88 0 (by decide +kernel)
  | exact S 14 88 1 (by decide +kernel)
  | exact S 14 88 2 (by decide +kernel)
  | exact S 14 88 3 (by decide +kernel)
  | exact S 14 88 4 (by decide +kernel)
  | exact S 14 88 5 (by decide +kernel)
theorem q14_89:ThresholdAt 14 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 89 0 (by decide +kernel)
  | exact S 14 89 1 (by decide +kernel)
  | exact S 14 89 2 (by decide +kernel)
  | exact S 14 89 3 (by decide +kernel)
  | exact S 14 89 4 (by decide +kernel)
  | exact S 14 89 5 (by decide +kernel)
theorem q14_90:ThresholdAt 14 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 90 0 (by decide +kernel)
  | exact S 14 90 1 (by decide +kernel)
  | exact S 14 90 2 (by decide +kernel)
  | exact S 14 90 3 (by decide +kernel)
  | exact S 14 90 4 (by decide +kernel)
  | exact S 14 90 5 (by decide +kernel)
theorem q14_91:ThresholdAt 14 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 91 0 (by decide +kernel)
  | exact S 14 91 1 (by decide +kernel)
  | exact S 14 91 2 (by decide +kernel)
  | exact S 14 91 3 (by decide +kernel)
  | exact S 14 91 4 (by decide +kernel)
  | exact S 14 91 5 (by decide +kernel)
theorem q14_92:ThresholdAt 14 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 92 0 (by decide +kernel)
  | exact S 14 92 1 (by decide +kernel)
  | exact S 14 92 2 (by decide +kernel)
  | exact S 14 92 3 (by decide +kernel)
  | exact S 14 92 4 (by decide +kernel)
  | exact S 14 92 5 (by decide +kernel)
theorem q14_93:ThresholdAt 14 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 93 0 (by decide +kernel)
  | exact S 14 93 1 (by decide +kernel)
  | exact S 14 93 2 (by decide +kernel)
  | exact S 14 93 3 (by decide +kernel)
  | exact S 14 93 4 (by decide +kernel)
  | exact S 14 93 5 (by decide +kernel)
theorem q14_94:ThresholdAt 14 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 94 0 (by decide +kernel)
  | exact S 14 94 1 (by decide +kernel)
  | exact S 14 94 2 (by decide +kernel)
  | exact S 14 94 3 (by decide +kernel)
  | exact S 14 94 4 (by decide +kernel)
  | exact S 14 94 5 (by decide +kernel)
theorem q14_95:ThresholdAt 14 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 95 0 (by decide +kernel)
  | exact S 14 95 1 (by decide +kernel)
  | exact S 14 95 2 (by decide +kernel)
  | exact S 14 95 3 (by decide +kernel)
  | exact S 14 95 4 (by decide +kernel)
  | exact S 14 95 5 (by decide +kernel)
theorem q14_96:ThresholdAt 14 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 96 0 (by decide +kernel)
  | exact S 14 96 1 (by decide +kernel)
  | exact S 14 96 2 (by decide +kernel)
  | exact S 14 96 3 (by decide +kernel)
  | exact S 14 96 4 (by decide +kernel)
  | exact S 14 96 5 (by decide +kernel)
theorem q14_97:ThresholdAt 14 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 97 0 (by decide +kernel)
  | exact S 14 97 1 (by decide +kernel)
  | exact S 14 97 2 (by decide +kernel)
  | exact S 14 97 3 (by decide +kernel)
  | exact S 14 97 4 (by decide +kernel)
  | exact S 14 97 5 (by decide +kernel)
theorem q14_98:ThresholdAt 14 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 98 0 (by decide +kernel)
  | exact S 14 98 1 (by decide +kernel)
  | exact S 14 98 2 (by decide +kernel)
  | exact S 14 98 3 (by decide +kernel)
  | exact S 14 98 4 (by decide +kernel)
  | exact S 14 98 5 (by decide +kernel)
theorem q14_99:ThresholdAt 14 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 99 0 (by decide +kernel)
  | exact S 14 99 1 (by decide +kernel)
  | exact S 14 99 2 (by decide +kernel)
  | exact S 14 99 3 (by decide +kernel)
  | exact S 14 99 4 (by decide +kernel)
  | exact S 14 99 5 (by decide +kernel)
theorem q14_100:ThresholdAt 14 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 100 0 (by decide +kernel)
  | exact S 14 100 1 (by decide +kernel)
  | exact S 14 100 2 (by decide +kernel)
  | exact S 14 100 3 (by decide +kernel)
  | exact S 14 100 4 (by decide +kernel)
  | exact S 14 100 5 (by decide +kernel)
theorem q14_101:ThresholdAt 14 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 101 0 (by decide +kernel)
  | exact S 14 101 1 (by decide +kernel)
  | exact S 14 101 2 (by decide +kernel)
  | exact S 14 101 3 (by decide +kernel)
  | exact S 14 101 4 (by decide +kernel)
  | exact S 14 101 5 (by decide +kernel)
theorem q14_102:ThresholdAt 14 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 102 0 (by decide +kernel)
  | exact S 14 102 1 (by decide +kernel)
  | exact S 14 102 2 (by decide +kernel)
  | exact S 14 102 3 (by decide +kernel)
  | exact S 14 102 4 (by decide +kernel)
  | exact S 14 102 5 (by decide +kernel)
theorem q14_103:ThresholdAt 14 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 103 0 (by decide +kernel)
  | exact S 14 103 1 (by decide +kernel)
  | exact S 14 103 2 (by decide +kernel)
  | exact S 14 103 3 (by decide +kernel)
  | exact S 14 103 4 (by decide +kernel)
  | exact S 14 103 5 (by decide +kernel)
theorem q14_104:ThresholdAt 14 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 104 0 (by decide +kernel)
  | exact S 14 104 1 (by decide +kernel)
  | exact S 14 104 2 (by decide +kernel)
  | exact S 14 104 3 (by decide +kernel)
  | exact S 14 104 4 (by decide +kernel)
  | exact S 14 104 5 (by decide +kernel)
theorem q14_105:ThresholdAt 14 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 105 0 (by decide +kernel)
  | exact S 14 105 1 (by decide +kernel)
  | exact S 14 105 2 (by decide +kernel)
  | exact S 14 105 3 (by decide +kernel)
  | exact S 14 105 4 (by decide +kernel)
  | exact S 14 105 5 (by decide +kernel)
theorem q14_106:ThresholdAt 14 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 106 0 (by decide +kernel)
  | exact S 14 106 1 (by decide +kernel)
  | exact S 14 106 2 (by decide +kernel)
  | exact S 14 106 3 (by decide +kernel)
  | exact S 14 106 4 (by decide +kernel)
  | exact S 14 106 5 (by decide +kernel)
theorem q14_107:ThresholdAt 14 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 107 0 (by decide +kernel)
  | exact S 14 107 1 (by decide +kernel)
  | exact S 14 107 2 (by decide +kernel)
  | exact S 14 107 3 (by decide +kernel)
  | exact S 14 107 4 (by decide +kernel)
  | exact S 14 107 5 (by decide +kernel)
theorem q14_108:ThresholdAt 14 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 108 0 (by decide +kernel)
  | exact S 14 108 1 (by decide +kernel)
  | exact S 14 108 2 (by decide +kernel)
  | exact S 14 108 3 (by decide +kernel)
  | exact S 14 108 4 (by decide +kernel)
  | exact S 14 108 5 (by decide +kernel)
theorem q14_109:ThresholdAt 14 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 109 0 (by decide +kernel)
  | exact S 14 109 1 (by decide +kernel)
  | exact S 14 109 2 (by decide +kernel)
  | exact S 14 109 3 (by decide +kernel)
  | exact S 14 109 4 (by decide +kernel)
  | exact S 14 109 5 (by decide +kernel)
theorem q14_110:ThresholdAt 14 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 110 0 (by decide +kernel)
  | exact S 14 110 1 (by decide +kernel)
  | exact S 14 110 2 (by decide +kernel)
  | exact S 14 110 3 (by decide +kernel)
  | exact S 14 110 4 (by decide +kernel)
  | exact S 14 110 5 (by decide +kernel)
theorem q14_111:ThresholdAt 14 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 111 0 (by decide +kernel)
  | exact S 14 111 1 (by decide +kernel)
  | exact S 14 111 2 (by decide +kernel)
  | exact S 14 111 3 (by decide +kernel)
  | exact S 14 111 4 (by decide +kernel)
  | exact S 14 111 5 (by decide +kernel)
theorem q14_112:ThresholdAt 14 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 112 0 (by decide +kernel)
  | exact S 14 112 1 (by decide +kernel)
  | exact S 14 112 2 (by decide +kernel)
  | exact S 14 112 3 (by decide +kernel)
  | exact S 14 112 4 (by decide +kernel)
  | exact S 14 112 5 (by decide +kernel)
theorem q14_113:ThresholdAt 14 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 113 0 (by decide +kernel)
  | exact S 14 113 1 (by decide +kernel)
  | exact S 14 113 2 (by decide +kernel)
  | exact S 14 113 3 (by decide +kernel)
  | exact S 14 113 4 (by decide +kernel)
  | exact S 14 113 5 (by decide +kernel)
theorem q14_114:ThresholdAt 14 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 114 0 (by decide +kernel)
  | exact S 14 114 1 (by decide +kernel)
  | exact S 14 114 2 (by decide +kernel)
  | exact S 14 114 3 (by decide +kernel)
  | exact S 14 114 4 (by decide +kernel)
  | exact S 14 114 5 (by decide +kernel)
theorem q14_115:ThresholdAt 14 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 115 0 (by decide +kernel)
  | exact S 14 115 1 (by decide +kernel)
  | exact S 14 115 2 (by decide +kernel)
  | exact S 14 115 3 (by decide +kernel)
  | exact S 14 115 4 (by decide +kernel)
  | exact S 14 115 5 (by decide +kernel)
theorem q14_116:ThresholdAt 14 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 116 0 (by decide +kernel)
  | exact S 14 116 1 (by decide +kernel)
  | exact S 14 116 2 (by decide +kernel)
  | exact S 14 116 3 (by decide +kernel)
  | exact S 14 116 4 (by decide +kernel)
  | exact S 14 116 5 (by decide +kernel)
theorem q14_117:ThresholdAt 14 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 117 0 (by decide +kernel)
  | exact S 14 117 1 (by decide +kernel)
  | exact S 14 117 2 (by decide +kernel)
  | exact S 14 117 3 (by decide +kernel)
  | exact S 14 117 4 (by decide +kernel)
  | exact S 14 117 5 (by decide +kernel)
theorem q14_118:ThresholdAt 14 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 118 0 (by decide +kernel)
  | exact S 14 118 1 (by decide +kernel)
  | exact S 14 118 2 (by decide +kernel)
  | exact S 14 118 3 (by decide +kernel)
  | exact S 14 118 4 (by decide +kernel)
  | exact S 14 118 5 (by decide +kernel)
theorem q14_119:ThresholdAt 14 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 119 0 (by decide +kernel)
  | exact S 14 119 1 (by decide +kernel)
  | exact S 14 119 2 (by decide +kernel)
  | exact S 14 119 3 (by decide +kernel)
  | exact S 14 119 4 (by decide +kernel)
  | exact S 14 119 5 (by decide +kernel)
theorem q14_120:ThresholdAt 14 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 120 0 (by decide +kernel)
  | exact S 14 120 1 (by decide +kernel)
  | exact S 14 120 2 (by decide +kernel)
  | exact S 14 120 3 (by decide +kernel)
  | exact S 14 120 4 (by decide +kernel)
  | exact S 14 120 5 (by decide +kernel)
theorem q14_121:ThresholdAt 14 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 121 0 (by decide +kernel)
  | exact S 14 121 1 (by decide +kernel)
  | exact S 14 121 2 (by decide +kernel)
  | exact S 14 121 3 (by decide +kernel)
  | exact S 14 121 4 (by decide +kernel)
  | exact S 14 121 5 (by decide +kernel)
theorem q14_122:ThresholdAt 14 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 122 0 (by decide +kernel)
  | exact S 14 122 1 (by decide +kernel)
  | exact S 14 122 2 (by decide +kernel)
  | exact S 14 122 3 (by decide +kernel)
  | exact S 14 122 4 (by decide +kernel)
  | exact S 14 122 5 (by decide +kernel)
theorem q14_123:ThresholdAt 14 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 123 0 (by decide +kernel)
  | exact S 14 123 1 (by decide +kernel)
  | exact S 14 123 2 (by decide +kernel)
  | exact S 14 123 3 (by decide +kernel)
  | exact S 14 123 4 (by decide +kernel)
  | exact S 14 123 5 (by decide +kernel)
theorem q14_124:ThresholdAt 14 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 124 0 (by decide +kernel)
  | exact S 14 124 1 (by decide +kernel)
  | exact S 14 124 2 (by decide +kernel)
  | exact S 14 124 3 (by decide +kernel)
  | exact S 14 124 4 (by decide +kernel)
  | exact S 14 124 5 (by decide +kernel)
theorem q14_125:ThresholdAt 14 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 125 0 (by decide +kernel)
  | exact S 14 125 1 (by decide +kernel)
  | exact S 14 125 2 (by decide +kernel)
  | exact S 14 125 3 (by decide +kernel)
  | exact S 14 125 4 (by decide +kernel)
  | exact S 14 125 5 (by decide +kernel)
theorem q14_126:ThresholdAt 14 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 126 0 (by decide +kernel)
  | exact S 14 126 1 (by decide +kernel)
  | exact S 14 126 2 (by decide +kernel)
  | exact S 14 126 3 (by decide +kernel)
  | exact S 14 126 4 (by decide +kernel)
  | exact S 14 126 5 (by decide +kernel)
theorem q14_127:ThresholdAt 14 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 127 0 (by decide +kernel)
  | exact S 14 127 1 (by decide +kernel)
  | exact S 14 127 2 (by decide +kernel)
  | exact S 14 127 3 (by decide +kernel)
  | exact S 14 127 4 (by decide +kernel)
  | exact S 14 127 5 (by decide +kernel)
theorem q14_128:ThresholdAt 14 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 14 128 0 (by decide +kernel)
  | exact S 14 128 1 (by decide +kernel)
  | exact S 14 128 2 (by decide +kernel)
  | exact S 14 128 3 (by decide +kernel)
  | exact S 14 128 4 (by decide +kernel)
  | exact S 14 128 5 (by decide +kernel)
theorem checkedR14:∀ V ∈ List.range 129,ThresholdAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0_129:V < 64
  · by_cases h0_64:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q14_0
              · have he:V = 1:=by omega
                subst V
                exact q14_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q14_2
              · have he:V = 3:=by omega
                subst V
                exact q14_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q14_4
              · have he:V = 5:=by omega
                subst V
                exact q14_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q14_6
              · have he:V = 7:=by omega
                subst V
                exact q14_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q14_8
              · have he:V = 9:=by omega
                subst V
                exact q14_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q14_10
              · have he:V = 11:=by omega
                subst V
                exact q14_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q14_12
              · have he:V = 13:=by omega
                subst V
                exact q14_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q14_14
              · have he:V = 15:=by omega
                subst V
                exact q14_15
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q14_16
              · have he:V = 17:=by omega
                subst V
                exact q14_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q14_18
              · have he:V = 19:=by omega
                subst V
                exact q14_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q14_20
              · have he:V = 21:=by omega
                subst V
                exact q14_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q14_22
              · have he:V = 23:=by omega
                subst V
                exact q14_23
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q14_24
              · have he:V = 25:=by omega
                subst V
                exact q14_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q14_26
              · have he:V = 27:=by omega
                subst V
                exact q14_27
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q14_28
              · have he:V = 29:=by omega
                subst V
                exact q14_29
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q14_30
              · have he:V = 31:=by omega
                subst V
                exact q14_31
    · by_cases h32_64:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q14_32
              · have he:V = 33:=by omega
                subst V
                exact q14_33
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q14_34
              · have he:V = 35:=by omega
                subst V
                exact q14_35
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q14_36
              · have he:V = 37:=by omega
                subst V
                exact q14_37
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q14_38
              · have he:V = 39:=by omega
                subst V
                exact q14_39
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q14_40
              · have he:V = 41:=by omega
                subst V
                exact q14_41
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q14_42
              · have he:V = 43:=by omega
                subst V
                exact q14_43
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q14_44
              · have he:V = 45:=by omega
                subst V
                exact q14_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q14_46
              · have he:V = 47:=by omega
                subst V
                exact q14_47
      · by_cases h48_64:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q14_48
              · have he:V = 49:=by omega
                subst V
                exact q14_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q14_50
              · have he:V = 51:=by omega
                subst V
                exact q14_51
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q14_52
              · have he:V = 53:=by omega
                subst V
                exact q14_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q14_54
              · have he:V = 55:=by omega
                subst V
                exact q14_55
        · by_cases h56_64:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q14_56
              · have he:V = 57:=by omega
                subst V
                exact q14_57
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q14_58
              · have he:V = 59:=by omega
                subst V
                exact q14_59
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q14_60
              · have he:V = 61:=by omega
                subst V
                exact q14_61
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q14_62
              · have he:V = 63:=by omega
                subst V
                exact q14_63
  · by_cases h64_129:V < 96
    · by_cases h64_96:V < 80
      · by_cases h64_80:V < 72
        · by_cases h64_72:V < 68
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q14_64
              · have he:V = 65:=by omega
                subst V
                exact q14_65
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q14_66
              · have he:V = 67:=by omega
                subst V
                exact q14_67
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q14_68
              · have he:V = 69:=by omega
                subst V
                exact q14_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q14_70
              · have he:V = 71:=by omega
                subst V
                exact q14_71
        · by_cases h72_80:V < 76
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q14_72
              · have he:V = 73:=by omega
                subst V
                exact q14_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q14_74
              · have he:V = 75:=by omega
                subst V
                exact q14_75
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q14_76
              · have he:V = 77:=by omega
                subst V
                exact q14_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q14_78
              · have he:V = 79:=by omega
                subst V
                exact q14_79
      · by_cases h80_96:V < 88
        · by_cases h80_88:V < 84
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q14_80
              · have he:V = 81:=by omega
                subst V
                exact q14_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q14_82
              · have he:V = 83:=by omega
                subst V
                exact q14_83
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q14_84
              · have he:V = 85:=by omega
                subst V
                exact q14_85
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q14_86
              · have he:V = 87:=by omega
                subst V
                exact q14_87
        · by_cases h88_96:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q14_88
              · have he:V = 89:=by omega
                subst V
                exact q14_89
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q14_90
              · have he:V = 91:=by omega
                subst V
                exact q14_91
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q14_92
              · have he:V = 93:=by omega
                subst V
                exact q14_93
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q14_94
              · have he:V = 95:=by omega
                subst V
                exact q14_95
    · by_cases h96_129:V < 112
      · by_cases h96_112:V < 104
        · by_cases h96_104:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q14_96
              · have he:V = 97:=by omega
                subst V
                exact q14_97
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q14_98
              · have he:V = 99:=by omega
                subst V
                exact q14_99
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q14_100
              · have he:V = 101:=by omega
                subst V
                exact q14_101
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q14_102
              · have he:V = 103:=by omega
                subst V
                exact q14_103
        · by_cases h104_112:V < 108
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q14_104
              · have he:V = 105:=by omega
                subst V
                exact q14_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q14_106
              · have he:V = 107:=by omega
                subst V
                exact q14_107
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q14_108
              · have he:V = 109:=by omega
                subst V
                exact q14_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q14_110
              · have he:V = 111:=by omega
                subst V
                exact q14_111
      · by_cases h112_129:V < 120
        · by_cases h112_120:V < 116
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q14_112
              · have he:V = 113:=by omega
                subst V
                exact q14_113
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q14_114
              · have he:V = 115:=by omega
                subst V
                exact q14_115
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q14_116
              · have he:V = 117:=by omega
                subst V
                exact q14_117
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q14_118
              · have he:V = 119:=by omega
                subst V
                exact q14_119
        · by_cases h120_129:V < 124
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q14_120
              · have he:V = 121:=by omega
                subst V
                exact q14_121
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q14_122
              · have he:V = 123:=by omega
                subst V
                exact q14_123
          · by_cases h124_129:V < 126
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q14_124
              · have he:V = 125:=by omega
                subst V
                exact q14_125
            · by_cases h126_129:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q14_126
              · by_cases h127_129:V < 128
                · have he:V = 127:=by omega
                  subst V
                  exact q14_127
                · have he:V = 128:=by omega
                  subst V
                  exact q14_128
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
