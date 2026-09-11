import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked05

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q6_0:ThresholdAt 6 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 0 0 (by decide +kernel)
  | exact S 6 0 1 (by decide +kernel)
  | exact S 6 0 2 (by decide +kernel)
  | exact S 6 0 3 (by decide +kernel)
  | exact S 6 0 4 (by decide +kernel)
  | exact S 6 0 5 (by decide +kernel)
theorem q6_1:ThresholdAt 6 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 1 0 (by decide +kernel)
  | exact S 6 1 1 (by decide +kernel)
  | exact S 6 1 2 (by decide +kernel)
  | exact S 6 1 3 (by decide +kernel)
  | exact S 6 1 4 (by decide +kernel)
  | exact S 6 1 5 (by decide +kernel)
theorem q6_2:ThresholdAt 6 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 2 0 (by decide +kernel)
  | exact S 6 2 1 (by decide +kernel)
  | exact S 6 2 2 (by decide +kernel)
  | exact S 6 2 3 (by decide +kernel)
  | exact S 6 2 4 (by decide +kernel)
  | exact S 6 2 5 (by decide +kernel)
theorem q6_3:ThresholdAt 6 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 3 0 (by decide +kernel)
  | exact S 6 3 1 (by decide +kernel)
  | exact S 6 3 2 (by decide +kernel)
  | exact S 6 3 3 (by decide +kernel)
  | exact S 6 3 4 (by decide +kernel)
  | exact S 6 3 5 (by decide +kernel)
theorem q6_4:ThresholdAt 6 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 4 0 (by decide +kernel)
  | exact S 6 4 1 (by decide +kernel)
  | exact S 6 4 2 (by decide +kernel)
  | exact S 6 4 3 (by decide +kernel)
  | exact S 6 4 4 (by decide +kernel)
  | exact S 6 4 5 (by decide +kernel)
theorem q6_5:ThresholdAt 6 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 5 0 (by decide +kernel)
  | exact S 6 5 1 (by decide +kernel)
  | exact S 6 5 2 (by decide +kernel)
  | exact S 6 5 3 (by decide +kernel)
  | exact S 6 5 4 (by decide +kernel)
  | exact S 6 5 5 (by decide +kernel)
theorem q6_6:ThresholdAt 6 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 6 0 (by decide +kernel)
  | exact S 6 6 1 (by decide +kernel)
  | exact S 6 6 2 (by decide +kernel)
  | exact S 6 6 3 (by decide +kernel)
  | exact S 6 6 4 (by decide +kernel)
  | exact S 6 6 5 (by decide +kernel)
theorem q6_7:ThresholdAt 6 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 7 0 (by decide +kernel)
  | exact S 6 7 1 (by decide +kernel)
  | exact S 6 7 2 (by decide +kernel)
  | exact S 6 7 3 (by decide +kernel)
  | exact S 6 7 4 (by decide +kernel)
  | exact S 6 7 5 (by decide +kernel)
theorem q6_8:ThresholdAt 6 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 8 0 (by decide +kernel)
  | exact S 6 8 1 (by decide +kernel)
  | exact S 6 8 2 (by decide +kernel)
  | exact S 6 8 3 (by decide +kernel)
  | exact S 6 8 4 (by decide +kernel)
  | exact S 6 8 5 (by decide +kernel)
theorem q6_9:ThresholdAt 6 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 9 0 (by decide +kernel)
  | exact S 6 9 1 (by decide +kernel)
  | exact S 6 9 2 (by decide +kernel)
  | exact S 6 9 3 (by decide +kernel)
  | exact S 6 9 4 (by decide +kernel)
  | exact S 6 9 5 (by decide +kernel)
theorem q6_10:ThresholdAt 6 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 10 0 (by decide +kernel)
  | exact S 6 10 1 (by decide +kernel)
  | exact S 6 10 2 (by decide +kernel)
  | exact S 6 10 3 (by decide +kernel)
  | exact S 6 10 4 (by decide +kernel)
  | exact S 6 10 5 (by decide +kernel)
theorem q6_11:ThresholdAt 6 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 11 0 (by decide +kernel)
  | exact S 6 11 1 (by decide +kernel)
  | exact S 6 11 2 (by decide +kernel)
  | exact S 6 11 3 (by decide +kernel)
  | exact S 6 11 4 (by decide +kernel)
  | exact S 6 11 5 (by decide +kernel)
theorem q6_12:ThresholdAt 6 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 12 0 (by decide +kernel)
  | exact S 6 12 1 (by decide +kernel)
  | exact S 6 12 2 (by decide +kernel)
  | exact S 6 12 3 (by decide +kernel)
  | exact S 6 12 4 (by decide +kernel)
  | exact S 6 12 5 (by decide +kernel)
theorem q6_13:ThresholdAt 6 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 13 0 (by decide +kernel)
  | exact S 6 13 1 (by decide +kernel)
  | exact S 6 13 2 (by decide +kernel)
  | exact S 6 13 3 (by decide +kernel)
  | exact S 6 13 4 (by decide +kernel)
  | exact S 6 13 5 (by decide +kernel)
theorem q6_14:ThresholdAt 6 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 14 0 (by decide +kernel)
  | exact S 6 14 1 (by decide +kernel)
  | exact S 6 14 2 (by decide +kernel)
  | exact S 6 14 3 (by decide +kernel)
  | exact S 6 14 4 (by decide +kernel)
  | exact S 6 14 5 (by decide +kernel)
theorem q6_15:ThresholdAt 6 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 15 0 (by decide +kernel)
  | exact S 6 15 1 (by decide +kernel)
  | exact S 6 15 2 (by decide +kernel)
  | exact S 6 15 3 (by decide +kernel)
  | exact S 6 15 4 (by decide +kernel)
  | exact S 6 15 5 (by decide +kernel)
theorem q6_16:ThresholdAt 6 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 16 0 (by decide +kernel)
  | exact S 6 16 1 (by decide +kernel)
  | exact S 6 16 2 (by decide +kernel)
  | exact S 6 16 3 (by decide +kernel)
  | exact S 6 16 4 (by decide +kernel)
  | exact S 6 16 5 (by decide +kernel)
theorem q6_17:ThresholdAt 6 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 17 0 (by decide +kernel)
  | exact S 6 17 1 (by decide +kernel)
  | exact S 6 17 2 (by decide +kernel)
  | exact S 6 17 3 (by decide +kernel)
  | exact S 6 17 4 (by decide +kernel)
  | exact S 6 17 5 (by decide +kernel)
theorem q6_18:ThresholdAt 6 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 18 0 (by decide +kernel)
  | exact S 6 18 1 (by decide +kernel)
  | exact S 6 18 2 (by decide +kernel)
  | exact S 6 18 3 (by decide +kernel)
  | exact S 6 18 4 (by decide +kernel)
  | exact S 6 18 5 (by decide +kernel)
theorem q6_19:ThresholdAt 6 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 19 0 (by decide +kernel)
  | exact S 6 19 1 (by decide +kernel)
  | exact S 6 19 2 (by decide +kernel)
  | exact S 6 19 3 (by decide +kernel)
  | exact S 6 19 4 (by decide +kernel)
  | exact S 6 19 5 (by decide +kernel)
theorem q6_20:ThresholdAt 6 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 20 0 (by decide +kernel)
  | exact S 6 20 1 (by decide +kernel)
  | exact S 6 20 2 (by decide +kernel)
  | exact S 6 20 3 (by decide +kernel)
  | exact S 6 20 4 (by decide +kernel)
  | exact S 6 20 5 (by decide +kernel)
theorem q6_21:ThresholdAt 6 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 21 0 (by decide +kernel)
  | exact S 6 21 1 (by decide +kernel)
  | exact S 6 21 2 (by decide +kernel)
  | exact S 6 21 3 (by decide +kernel)
  | exact S 6 21 4 (by decide +kernel)
  | exact S 6 21 5 (by decide +kernel)
theorem q6_22:ThresholdAt 6 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 22 0 (by decide +kernel)
  | exact S 6 22 1 (by decide +kernel)
  | exact S 6 22 2 (by decide +kernel)
  | exact S 6 22 3 (by decide +kernel)
  | exact S 6 22 4 (by decide +kernel)
  | exact S 6 22 5 (by decide +kernel)
theorem q6_23:ThresholdAt 6 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 23 0 (by decide +kernel)
  | exact S 6 23 1 (by decide +kernel)
  | exact S 6 23 2 (by decide +kernel)
  | exact S 6 23 3 (by decide +kernel)
  | exact S 6 23 4 (by decide +kernel)
  | exact S 6 23 5 (by decide +kernel)
theorem q6_24:ThresholdAt 6 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 24 0 (by decide +kernel)
  | exact S 6 24 1 (by decide +kernel)
  | exact S 6 24 2 (by decide +kernel)
  | exact S 6 24 3 (by decide +kernel)
  | exact S 6 24 4 (by decide +kernel)
  | exact S 6 24 5 (by decide +kernel)
theorem q6_25:ThresholdAt 6 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 25 0 (by decide +kernel)
  | exact S 6 25 1 (by decide +kernel)
  | exact S 6 25 2 (by decide +kernel)
  | exact S 6 25 3 (by decide +kernel)
  | exact S 6 25 4 (by decide +kernel)
  | exact S 6 25 5 (by decide +kernel)
theorem q6_26:ThresholdAt 6 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 26 0 (by decide +kernel)
  | exact S 6 26 1 (by decide +kernel)
  | exact S 6 26 2 (by decide +kernel)
  | exact S 6 26 3 (by decide +kernel)
  | exact S 6 26 4 (by decide +kernel)
  | exact S 6 26 5 (by decide +kernel)
theorem q6_27:ThresholdAt 6 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 27 0 (by decide +kernel)
  | exact S 6 27 1 (by decide +kernel)
  | exact S 6 27 2 (by decide +kernel)
  | exact S 6 27 3 (by decide +kernel)
  | exact S 6 27 4 (by decide +kernel)
  | exact S 6 27 5 (by decide +kernel)
theorem q6_28:ThresholdAt 6 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 28 0 (by decide +kernel)
  | exact S 6 28 1 (by decide +kernel)
  | exact S 6 28 2 (by decide +kernel)
  | exact S 6 28 3 (by decide +kernel)
  | exact S 6 28 4 (by decide +kernel)
  | exact S 6 28 5 (by decide +kernel)
theorem q6_29:ThresholdAt 6 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 29 0 (by decide +kernel)
  | exact S 6 29 1 (by decide +kernel)
  | exact S 6 29 2 (by decide +kernel)
  | exact S 6 29 3 (by decide +kernel)
  | exact S 6 29 4 (by decide +kernel)
  | exact S 6 29 5 (by decide +kernel)
theorem q6_30:ThresholdAt 6 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 30 0 (by decide +kernel)
  | exact S 6 30 1 (by decide +kernel)
  | exact S 6 30 2 (by decide +kernel)
  | exact S 6 30 3 (by decide +kernel)
  | exact S 6 30 4 (by decide +kernel)
  | exact S 6 30 5 (by decide +kernel)
theorem q6_31:ThresholdAt 6 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 31 0 (by decide +kernel)
  | exact S 6 31 1 (by decide +kernel)
  | exact S 6 31 2 (by decide +kernel)
  | exact S 6 31 3 (by decide +kernel)
  | exact S 6 31 4 (by decide +kernel)
  | exact S 6 31 5 (by decide +kernel)
theorem q6_32:ThresholdAt 6 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 32 0 (by decide +kernel)
  | exact S 6 32 1 (by decide +kernel)
  | exact S 6 32 2 (by decide +kernel)
  | exact S 6 32 3 (by decide +kernel)
  | exact S 6 32 4 (by decide +kernel)
  | exact S 6 32 5 (by decide +kernel)
theorem q6_33:ThresholdAt 6 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 33 0 (by decide +kernel)
  | exact S 6 33 1 (by decide +kernel)
  | exact S 6 33 2 (by decide +kernel)
  | exact S 6 33 3 (by decide +kernel)
  | exact S 6 33 4 (by decide +kernel)
  | exact S 6 33 5 (by decide +kernel)
theorem q6_34:ThresholdAt 6 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 34 0 (by decide +kernel)
  | exact S 6 34 1 (by decide +kernel)
  | exact S 6 34 2 (by decide +kernel)
  | exact S 6 34 3 (by decide +kernel)
  | exact S 6 34 4 (by decide +kernel)
  | exact S 6 34 5 (by decide +kernel)
theorem q6_35:ThresholdAt 6 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 35 0 (by decide +kernel)
  | exact S 6 35 1 (by decide +kernel)
  | exact S 6 35 2 (by decide +kernel)
  | exact S 6 35 3 (by decide +kernel)
  | exact S 6 35 4 (by decide +kernel)
  | exact S 6 35 5 (by decide +kernel)
theorem q6_36:ThresholdAt 6 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 36 0 (by decide +kernel)
  | exact S 6 36 1 (by decide +kernel)
  | exact S 6 36 2 (by decide +kernel)
  | exact S 6 36 3 (by decide +kernel)
  | exact S 6 36 4 (by decide +kernel)
  | exact S 6 36 5 (by decide +kernel)
theorem q6_37:ThresholdAt 6 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 37 0 (by decide +kernel)
  | exact S 6 37 1 (by decide +kernel)
  | exact S 6 37 2 (by decide +kernel)
  | exact S 6 37 3 (by decide +kernel)
  | exact S 6 37 4 (by decide +kernel)
  | exact S 6 37 5 (by decide +kernel)
theorem q6_38:ThresholdAt 6 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 38 0 (by decide +kernel)
  | exact S 6 38 1 (by decide +kernel)
  | exact S 6 38 2 (by decide +kernel)
  | exact S 6 38 3 (by decide +kernel)
  | exact S 6 38 4 (by decide +kernel)
  | exact S 6 38 5 (by decide +kernel)
theorem q6_39:ThresholdAt 6 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 39 0 (by decide +kernel)
  | exact S 6 39 1 (by decide +kernel)
  | exact S 6 39 2 (by decide +kernel)
  | exact S 6 39 3 (by decide +kernel)
  | exact S 6 39 4 (by decide +kernel)
  | exact S 6 39 5 (by decide +kernel)
theorem q6_40:ThresholdAt 6 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 40 0 (by decide +kernel)
  | exact S 6 40 1 (by decide +kernel)
  | exact S 6 40 2 (by decide +kernel)
  | exact S 6 40 3 (by decide +kernel)
  | exact S 6 40 4 (by decide +kernel)
  | exact S 6 40 5 (by decide +kernel)
theorem q6_41:ThresholdAt 6 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 41 0 (by decide +kernel)
  | exact S 6 41 1 (by decide +kernel)
  | exact S 6 41 2 (by decide +kernel)
  | exact S 6 41 3 (by decide +kernel)
  | exact S 6 41 4 (by decide +kernel)
  | exact S 6 41 5 (by decide +kernel)
theorem q6_42:ThresholdAt 6 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 42 0 (by decide +kernel)
  | exact S 6 42 1 (by decide +kernel)
  | exact S 6 42 2 (by decide +kernel)
  | exact S 6 42 3 (by decide +kernel)
  | exact S 6 42 4 (by decide +kernel)
  | exact S 6 42 5 (by decide +kernel)
theorem q6_43:ThresholdAt 6 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 43 0 (by decide +kernel)
  | exact S 6 43 1 (by decide +kernel)
  | exact S 6 43 2 (by decide +kernel)
  | exact S 6 43 3 (by decide +kernel)
  | exact S 6 43 4 (by decide +kernel)
  | exact S 6 43 5 (by decide +kernel)
theorem q6_44:ThresholdAt 6 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 44 0 (by decide +kernel)
  | exact S 6 44 1 (by decide +kernel)
  | exact S 6 44 2 (by decide +kernel)
  | exact S 6 44 3 (by decide +kernel)
  | exact S 6 44 4 (by decide +kernel)
  | exact S 6 44 5 (by decide +kernel)
theorem q6_45:ThresholdAt 6 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 45 0 (by decide +kernel)
  | exact S 6 45 1 (by decide +kernel)
  | exact S 6 45 2 (by decide +kernel)
  | exact S 6 45 3 (by decide +kernel)
  | exact S 6 45 4 (by decide +kernel)
  | exact S 6 45 5 (by decide +kernel)
theorem q6_46:ThresholdAt 6 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 46 0 (by decide +kernel)
  | exact S 6 46 1 (by decide +kernel)
  | exact S 6 46 2 (by decide +kernel)
  | exact S 6 46 3 (by decide +kernel)
  | exact S 6 46 4 (by decide +kernel)
  | exact S 6 46 5 (by decide +kernel)
theorem q6_47:ThresholdAt 6 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 47 0 (by decide +kernel)
  | exact S 6 47 1 (by decide +kernel)
  | exact S 6 47 2 (by decide +kernel)
  | exact S 6 47 3 (by decide +kernel)
  | exact S 6 47 4 (by decide +kernel)
  | exact S 6 47 5 (by decide +kernel)
theorem q6_48:ThresholdAt 6 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 48 0 (by decide +kernel)
  | exact S 6 48 1 (by decide +kernel)
  | exact S 6 48 2 (by decide +kernel)
  | exact S 6 48 3 (by decide +kernel)
  | exact S 6 48 4 (by decide +kernel)
  | exact S 6 48 5 (by decide +kernel)
theorem q6_49:ThresholdAt 6 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 49 0 (by decide +kernel)
  | exact S 6 49 1 (by decide +kernel)
  | exact S 6 49 2 (by decide +kernel)
  | exact S 6 49 3 (by decide +kernel)
  | exact S 6 49 4 (by decide +kernel)
  | exact S 6 49 5 (by decide +kernel)
theorem q6_50:ThresholdAt 6 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 50 0 (by decide +kernel)
  | exact S 6 50 1 (by decide +kernel)
  | exact S 6 50 2 (by decide +kernel)
  | exact S 6 50 3 (by decide +kernel)
  | exact S 6 50 4 (by decide +kernel)
  | exact S 6 50 5 (by decide +kernel)
theorem q6_51:ThresholdAt 6 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 51 0 (by decide +kernel)
  | exact S 6 51 1 (by decide +kernel)
  | exact S 6 51 2 (by decide +kernel)
  | exact S 6 51 3 (by decide +kernel)
  | exact S 6 51 4 (by decide +kernel)
  | exact S 6 51 5 (by decide +kernel)
theorem q6_52:ThresholdAt 6 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 52 0 (by decide +kernel)
  | exact S 6 52 1 (by decide +kernel)
  | exact S 6 52 2 (by decide +kernel)
  | exact S 6 52 3 (by decide +kernel)
  | exact S 6 52 4 (by decide +kernel)
  | exact S 6 52 5 (by decide +kernel)
theorem q6_53:ThresholdAt 6 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 53 0 (by decide +kernel)
  | exact S 6 53 1 (by decide +kernel)
  | exact S 6 53 2 (by decide +kernel)
  | exact S 6 53 3 (by decide +kernel)
  | exact S 6 53 4 (by decide +kernel)
  | exact S 6 53 5 (by decide +kernel)
theorem q6_54:ThresholdAt 6 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 54 0 (by decide +kernel)
  | exact S 6 54 1 (by decide +kernel)
  | exact S 6 54 2 (by decide +kernel)
  | exact S 6 54 3 (by decide +kernel)
  | exact S 6 54 4 (by decide +kernel)
  | exact S 6 54 5 (by decide +kernel)
theorem q6_55:ThresholdAt 6 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 55 0 (by decide +kernel)
  | exact S 6 55 1 (by decide +kernel)
  | exact S 6 55 2 (by decide +kernel)
  | exact S 6 55 3 (by decide +kernel)
  | exact S 6 55 4 (by decide +kernel)
  | exact S 6 55 5 (by decide +kernel)
theorem q6_56:ThresholdAt 6 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 56 0 (by decide +kernel)
  | exact S 6 56 1 (by decide +kernel)
  | exact S 6 56 2 (by decide +kernel)
  | exact S 6 56 3 (by decide +kernel)
  | exact S 6 56 4 (by decide +kernel)
  | exact S 6 56 5 (by decide +kernel)
theorem q6_57:ThresholdAt 6 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 57 0 (by decide +kernel)
  | exact S 6 57 1 (by decide +kernel)
  | exact S 6 57 2 (by decide +kernel)
  | exact S 6 57 3 (by decide +kernel)
  | exact S 6 57 4 (by decide +kernel)
  | exact S 6 57 5 (by decide +kernel)
theorem q6_58:ThresholdAt 6 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 58 0 (by decide +kernel)
  | exact S 6 58 1 (by decide +kernel)
  | exact S 6 58 2 (by decide +kernel)
  | exact S 6 58 3 (by decide +kernel)
  | exact S 6 58 4 (by decide +kernel)
  | exact S 6 58 5 (by decide +kernel)
theorem q6_59:ThresholdAt 6 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 59 0 (by decide +kernel)
  | exact S 6 59 1 (by decide +kernel)
  | exact S 6 59 2 (by decide +kernel)
  | exact S 6 59 3 (by decide +kernel)
  | exact S 6 59 4 (by decide +kernel)
  | exact S 6 59 5 (by decide +kernel)
theorem q6_60:ThresholdAt 6 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 60 0 (by decide +kernel)
  | exact S 6 60 1 (by decide +kernel)
  | exact S 6 60 2 (by decide +kernel)
  | exact S 6 60 3 (by decide +kernel)
  | exact S 6 60 4 (by decide +kernel)
  | exact S 6 60 5 (by decide +kernel)
theorem q6_61:ThresholdAt 6 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 61 0 (by decide +kernel)
  | exact S 6 61 1 (by decide +kernel)
  | exact S 6 61 2 (by decide +kernel)
  | exact S 6 61 3 (by decide +kernel)
  | exact S 6 61 4 (by decide +kernel)
  | exact S 6 61 5 (by decide +kernel)
theorem q6_62:ThresholdAt 6 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 62 0 (by decide +kernel)
  | exact S 6 62 1 (by decide +kernel)
  | exact S 6 62 2 (by decide +kernel)
  | exact S 6 62 3 (by decide +kernel)
  | exact S 6 62 4 (by decide +kernel)
  | exact S 6 62 5 (by decide +kernel)
theorem q6_63:ThresholdAt 6 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 63 0 (by decide +kernel)
  | exact S 6 63 1 (by decide +kernel)
  | exact S 6 63 2 (by decide +kernel)
  | exact S 6 63 3 (by decide +kernel)
  | exact S 6 63 4 (by decide +kernel)
  | exact S 6 63 5 (by decide +kernel)
theorem q6_64:ThresholdAt 6 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 64 0 (by decide +kernel)
  | exact S 6 64 1 (by decide +kernel)
  | exact S 6 64 2 (by decide +kernel)
  | exact S 6 64 3 (by decide +kernel)
  | exact S 6 64 4 (by decide +kernel)
  | exact S 6 64 5 (by decide +kernel)
theorem q6_65:ThresholdAt 6 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 65 0 (by decide +kernel)
  | exact S 6 65 1 (by decide +kernel)
  | exact S 6 65 2 (by decide +kernel)
  | exact S 6 65 3 (by decide +kernel)
  | exact S 6 65 4 (by decide +kernel)
  | exact S 6 65 5 (by decide +kernel)
theorem q6_66:ThresholdAt 6 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 66 0 (by decide +kernel)
  | exact S 6 66 1 (by decide +kernel)
  | exact S 6 66 2 (by decide +kernel)
  | exact S 6 66 3 (by decide +kernel)
  | exact S 6 66 4 (by decide +kernel)
  | exact S 6 66 5 (by decide +kernel)
theorem q6_67:ThresholdAt 6 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 67 0 (by decide +kernel)
  | exact S 6 67 1 (by decide +kernel)
  | exact S 6 67 2 (by decide +kernel)
  | exact S 6 67 3 (by decide +kernel)
  | exact S 6 67 4 (by decide +kernel)
  | exact S 6 67 5 (by decide +kernel)
theorem q6_68:ThresholdAt 6 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 68 0 (by decide +kernel)
  | exact S 6 68 1 (by decide +kernel)
  | exact S 6 68 2 (by decide +kernel)
  | exact S 6 68 3 (by decide +kernel)
  | exact S 6 68 4 (by decide +kernel)
  | exact S 6 68 5 (by decide +kernel)
theorem q6_69:ThresholdAt 6 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 69 0 (by decide +kernel)
  | exact S 6 69 1 (by decide +kernel)
  | exact S 6 69 2 (by decide +kernel)
  | exact S 6 69 3 (by decide +kernel)
  | exact S 6 69 4 (by decide +kernel)
  | exact S 6 69 5 (by decide +kernel)
theorem q6_70:ThresholdAt 6 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 70 0 (by decide +kernel)
  | exact S 6 70 1 (by decide +kernel)
  | exact S 6 70 2 (by decide +kernel)
  | exact S 6 70 3 (by decide +kernel)
  | exact S 6 70 4 (by decide +kernel)
  | exact S 6 70 5 (by decide +kernel)
theorem q6_71:ThresholdAt 6 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 71 0 (by decide +kernel)
  | exact S 6 71 1 (by decide +kernel)
  | exact S 6 71 2 (by decide +kernel)
  | exact S 6 71 3 (by decide +kernel)
  | exact S 6 71 4 (by decide +kernel)
  | exact S 6 71 5 (by decide +kernel)
theorem q6_72:ThresholdAt 6 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 72 0 (by decide +kernel)
  | exact S 6 72 1 (by decide +kernel)
  | exact S 6 72 2 (by decide +kernel)
  | exact S 6 72 3 (by decide +kernel)
  | exact S 6 72 4 (by decide +kernel)
  | exact S 6 72 5 (by decide +kernel)
theorem q6_73:ThresholdAt 6 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 73 0 (by decide +kernel)
  | exact S 6 73 1 (by decide +kernel)
  | exact S 6 73 2 (by decide +kernel)
  | exact S 6 73 3 (by decide +kernel)
  | exact S 6 73 4 (by decide +kernel)
  | exact S 6 73 5 (by decide +kernel)
theorem q6_74:ThresholdAt 6 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 74 0 (by decide +kernel)
  | exact S 6 74 1 (by decide +kernel)
  | exact S 6 74 2 (by decide +kernel)
  | exact S 6 74 3 (by decide +kernel)
  | exact S 6 74 4 (by decide +kernel)
  | exact S 6 74 5 (by decide +kernel)
theorem q6_75:ThresholdAt 6 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 75 0 (by decide +kernel)
  | exact S 6 75 1 (by decide +kernel)
  | exact S 6 75 2 (by decide +kernel)
  | exact S 6 75 3 (by decide +kernel)
  | exact S 6 75 4 (by decide +kernel)
  | exact S 6 75 5 (by decide +kernel)
theorem q6_76:ThresholdAt 6 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 76 0 (by decide +kernel)
  | exact S 6 76 1 (by decide +kernel)
  | exact S 6 76 2 (by decide +kernel)
  | exact S 6 76 3 (by decide +kernel)
  | exact S 6 76 4 (by decide +kernel)
  | exact S 6 76 5 (by decide +kernel)
theorem q6_77:ThresholdAt 6 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 77 0 (by decide +kernel)
  | exact S 6 77 1 (by decide +kernel)
  | exact S 6 77 2 (by decide +kernel)
  | exact S 6 77 3 (by decide +kernel)
  | exact S 6 77 4 (by decide +kernel)
  | exact S 6 77 5 (by decide +kernel)
theorem q6_78:ThresholdAt 6 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 78 0 (by decide +kernel)
  | exact S 6 78 1 (by decide +kernel)
  | exact S 6 78 2 (by decide +kernel)
  | exact S 6 78 3 (by decide +kernel)
  | exact S 6 78 4 (by decide +kernel)
  | exact S 6 78 5 (by decide +kernel)
theorem q6_79:ThresholdAt 6 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 79 0 (by decide +kernel)
  | exact S 6 79 1 (by decide +kernel)
  | exact S 6 79 2 (by decide +kernel)
  | exact S 6 79 3 (by decide +kernel)
  | exact S 6 79 4 (by decide +kernel)
  | exact S 6 79 5 (by decide +kernel)
theorem q6_80:ThresholdAt 6 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 80 0 (by decide +kernel)
  | exact S 6 80 1 (by decide +kernel)
  | exact S 6 80 2 (by decide +kernel)
  | exact S 6 80 3 (by decide +kernel)
  | exact S 6 80 4 (by decide +kernel)
  | exact S 6 80 5 (by decide +kernel)
theorem q6_81:ThresholdAt 6 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 81 0 (by decide +kernel)
  | exact S 6 81 1 (by decide +kernel)
  | exact S 6 81 2 (by decide +kernel)
  | exact S 6 81 3 (by decide +kernel)
  | exact S 6 81 4 (by decide +kernel)
  | exact S 6 81 5 (by decide +kernel)
theorem q6_82:ThresholdAt 6 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 82 0 (by decide +kernel)
  | exact S 6 82 1 (by decide +kernel)
  | exact S 6 82 2 (by decide +kernel)
  | exact S 6 82 3 (by decide +kernel)
  | exact S 6 82 4 (by decide +kernel)
  | exact S 6 82 5 (by decide +kernel)
theorem q6_83:ThresholdAt 6 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 83 0 (by decide +kernel)
  | exact S 6 83 1 (by decide +kernel)
  | exact S 6 83 2 (by decide +kernel)
  | exact S 6 83 3 (by decide +kernel)
  | exact S 6 83 4 (by decide +kernel)
  | exact S 6 83 5 (by decide +kernel)
theorem q6_84:ThresholdAt 6 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 84 0 (by decide +kernel)
  | exact S 6 84 1 (by decide +kernel)
  | exact S 6 84 2 (by decide +kernel)
  | exact S 6 84 3 (by decide +kernel)
  | exact S 6 84 4 (by decide +kernel)
  | exact S 6 84 5 (by decide +kernel)
theorem q6_85:ThresholdAt 6 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 85 0 (by decide +kernel)
  | exact S 6 85 1 (by decide +kernel)
  | exact S 6 85 2 (by decide +kernel)
  | exact S 6 85 3 (by decide +kernel)
  | exact S 6 85 4 (by decide +kernel)
  | exact S 6 85 5 (by decide +kernel)
theorem q6_86:ThresholdAt 6 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 86 0 (by decide +kernel)
  | exact S 6 86 1 (by decide +kernel)
  | exact S 6 86 2 (by decide +kernel)
  | exact S 6 86 3 (by decide +kernel)
  | exact S 6 86 4 (by decide +kernel)
  | exact S 6 86 5 (by decide +kernel)
theorem q6_87:ThresholdAt 6 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 87 0 (by decide +kernel)
  | exact S 6 87 1 (by decide +kernel)
  | exact S 6 87 2 (by decide +kernel)
  | exact S 6 87 3 (by decide +kernel)
  | exact S 6 87 4 (by decide +kernel)
  | exact S 6 87 5 (by decide +kernel)
theorem q6_88:ThresholdAt 6 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 88 0 (by decide +kernel)
  | exact S 6 88 1 (by decide +kernel)
  | exact S 6 88 2 (by decide +kernel)
  | exact S 6 88 3 (by decide +kernel)
  | exact S 6 88 4 (by decide +kernel)
  | exact S 6 88 5 (by decide +kernel)
theorem q6_89:ThresholdAt 6 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 89 0 (by decide +kernel)
  | exact S 6 89 1 (by decide +kernel)
  | exact S 6 89 2 (by decide +kernel)
  | exact S 6 89 3 (by decide +kernel)
  | exact S 6 89 4 (by decide +kernel)
  | exact S 6 89 5 (by decide +kernel)
theorem q6_90:ThresholdAt 6 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 90 0 (by decide +kernel)
  | exact S 6 90 1 (by decide +kernel)
  | exact S 6 90 2 (by decide +kernel)
  | exact S 6 90 3 (by decide +kernel)
  | exact S 6 90 4 (by decide +kernel)
  | exact S 6 90 5 (by decide +kernel)
theorem q6_91:ThresholdAt 6 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 91 0 (by decide +kernel)
  | exact S 6 91 1 (by decide +kernel)
  | exact S 6 91 2 (by decide +kernel)
  | exact S 6 91 3 (by decide +kernel)
  | exact S 6 91 4 (by decide +kernel)
  | exact S 6 91 5 (by decide +kernel)
theorem q6_92:ThresholdAt 6 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 92 0 (by decide +kernel)
  | exact S 6 92 1 (by decide +kernel)
  | exact S 6 92 2 (by decide +kernel)
  | exact S 6 92 3 (by decide +kernel)
  | exact S 6 92 4 (by decide +kernel)
  | exact S 6 92 5 (by decide +kernel)
theorem q6_93:ThresholdAt 6 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 93 0 (by decide +kernel)
  | exact S 6 93 1 (by decide +kernel)
  | exact S 6 93 2 (by decide +kernel)
  | exact S 6 93 3 (by decide +kernel)
  | exact S 6 93 4 (by decide +kernel)
  | exact S 6 93 5 (by decide +kernel)
theorem q6_94:ThresholdAt 6 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 94 0 (by decide +kernel)
  | exact S 6 94 1 (by decide +kernel)
  | exact S 6 94 2 (by decide +kernel)
  | exact S 6 94 3 (by decide +kernel)
  | exact S 6 94 4 (by decide +kernel)
  | exact S 6 94 5 (by decide +kernel)
theorem q6_95:ThresholdAt 6 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 95 0 (by decide +kernel)
  | exact S 6 95 1 (by decide +kernel)
  | exact S 6 95 2 (by decide +kernel)
  | exact S 6 95 3 (by decide +kernel)
  | exact S 6 95 4 (by decide +kernel)
  | exact S 6 95 5 (by decide +kernel)
theorem q6_96:ThresholdAt 6 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 96 0 (by decide +kernel)
  | exact S 6 96 1 (by decide +kernel)
  | exact S 6 96 2 (by decide +kernel)
  | exact S 6 96 3 (by decide +kernel)
  | exact S 6 96 4 (by decide +kernel)
  | exact S 6 96 5 (by decide +kernel)
theorem q6_97:ThresholdAt 6 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 97 0 (by decide +kernel)
  | exact S 6 97 1 (by decide +kernel)
  | exact S 6 97 2 (by decide +kernel)
  | exact S 6 97 3 (by decide +kernel)
  | exact S 6 97 4 (by decide +kernel)
  | exact S 6 97 5 (by decide +kernel)
theorem q6_98:ThresholdAt 6 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 98 0 (by decide +kernel)
  | exact S 6 98 1 (by decide +kernel)
  | exact S 6 98 2 (by decide +kernel)
  | exact S 6 98 3 (by decide +kernel)
  | exact S 6 98 4 (by decide +kernel)
  | exact S 6 98 5 (by decide +kernel)
theorem q6_99:ThresholdAt 6 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 99 0 (by decide +kernel)
  | exact S 6 99 1 (by decide +kernel)
  | exact S 6 99 2 (by decide +kernel)
  | exact S 6 99 3 (by decide +kernel)
  | exact S 6 99 4 (by decide +kernel)
  | exact S 6 99 5 (by decide +kernel)
theorem q6_100:ThresholdAt 6 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 100 0 (by decide +kernel)
  | exact S 6 100 1 (by decide +kernel)
  | exact S 6 100 2 (by decide +kernel)
  | exact S 6 100 3 (by decide +kernel)
  | exact S 6 100 4 (by decide +kernel)
  | exact S 6 100 5 (by decide +kernel)
theorem q6_101:ThresholdAt 6 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 101 0 (by decide +kernel)
  | exact S 6 101 1 (by decide +kernel)
  | exact S 6 101 2 (by decide +kernel)
  | exact S 6 101 3 (by decide +kernel)
  | exact S 6 101 4 (by decide +kernel)
  | exact S 6 101 5 (by decide +kernel)
theorem q6_102:ThresholdAt 6 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 102 0 (by decide +kernel)
  | exact S 6 102 1 (by decide +kernel)
  | exact S 6 102 2 (by decide +kernel)
  | exact S 6 102 3 (by decide +kernel)
  | exact S 6 102 4 (by decide +kernel)
  | exact S 6 102 5 (by decide +kernel)
theorem q6_103:ThresholdAt 6 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 103 0 (by decide +kernel)
  | exact S 6 103 1 (by decide +kernel)
  | exact S 6 103 2 (by decide +kernel)
  | exact S 6 103 3 (by decide +kernel)
  | exact S 6 103 4 (by decide +kernel)
  | exact S 6 103 5 (by decide +kernel)
theorem q6_104:ThresholdAt 6 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 104 0 (by decide +kernel)
  | exact S 6 104 1 (by decide +kernel)
  | exact S 6 104 2 (by decide +kernel)
  | exact S 6 104 3 (by decide +kernel)
  | exact S 6 104 4 (by decide +kernel)
  | exact S 6 104 5 (by decide +kernel)
theorem q6_105:ThresholdAt 6 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 105 0 (by decide +kernel)
  | exact S 6 105 1 (by decide +kernel)
  | exact S 6 105 2 (by decide +kernel)
  | exact S 6 105 3 (by decide +kernel)
  | exact S 6 105 4 (by decide +kernel)
  | exact S 6 105 5 (by decide +kernel)
theorem q6_106:ThresholdAt 6 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 106 0 (by decide +kernel)
  | exact S 6 106 1 (by decide +kernel)
  | exact S 6 106 2 (by decide +kernel)
  | exact S 6 106 3 (by decide +kernel)
  | exact S 6 106 4 (by decide +kernel)
  | exact S 6 106 5 (by decide +kernel)
theorem q6_107:ThresholdAt 6 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 107 0 (by decide +kernel)
  | exact S 6 107 1 (by decide +kernel)
  | exact S 6 107 2 (by decide +kernel)
  | exact S 6 107 3 (by decide +kernel)
  | exact S 6 107 4 (by decide +kernel)
  | exact S 6 107 5 (by decide +kernel)
theorem q6_108:ThresholdAt 6 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 108 0 (by decide +kernel)
  | exact S 6 108 1 (by decide +kernel)
  | exact S 6 108 2 (by decide +kernel)
  | exact S 6 108 3 (by decide +kernel)
  | exact S 6 108 4 (by decide +kernel)
  | exact S 6 108 5 (by decide +kernel)
theorem q6_109:ThresholdAt 6 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 109 0 (by decide +kernel)
  | exact S 6 109 1 (by decide +kernel)
  | exact S 6 109 2 (by decide +kernel)
  | exact S 6 109 3 (by decide +kernel)
  | exact S 6 109 4 (by decide +kernel)
  | exact S 6 109 5 (by decide +kernel)
theorem q6_110:ThresholdAt 6 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 110 0 (by decide +kernel)
  | exact S 6 110 1 (by decide +kernel)
  | exact S 6 110 2 (by decide +kernel)
  | exact S 6 110 3 (by decide +kernel)
  | exact S 6 110 4 (by decide +kernel)
  | exact S 6 110 5 (by decide +kernel)
theorem q6_111:ThresholdAt 6 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 111 0 (by decide +kernel)
  | exact S 6 111 1 (by decide +kernel)
  | exact S 6 111 2 (by decide +kernel)
  | exact S 6 111 3 (by decide +kernel)
  | exact S 6 111 4 (by decide +kernel)
  | exact S 6 111 5 (by decide +kernel)
theorem q6_112:ThresholdAt 6 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 112 0 (by decide +kernel)
  | exact S 6 112 1 (by decide +kernel)
  | exact S 6 112 2 (by decide +kernel)
  | exact S 6 112 3 (by decide +kernel)
  | exact S 6 112 4 (by decide +kernel)
  | exact S 6 112 5 (by decide +kernel)
theorem q6_113:ThresholdAt 6 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 113 0 (by decide +kernel)
  | exact S 6 113 1 (by decide +kernel)
  | exact S 6 113 2 (by decide +kernel)
  | exact S 6 113 3 (by decide +kernel)
  | exact S 6 113 4 (by decide +kernel)
  | exact S 6 113 5 (by decide +kernel)
theorem q6_114:ThresholdAt 6 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 114 0 (by decide +kernel)
  | exact S 6 114 1 (by decide +kernel)
  | exact S 6 114 2 (by decide +kernel)
  | exact S 6 114 3 (by decide +kernel)
  | exact S 6 114 4 (by decide +kernel)
  | exact S 6 114 5 (by decide +kernel)
theorem q6_115:ThresholdAt 6 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 115 0 (by decide +kernel)
  | exact S 6 115 1 (by decide +kernel)
  | exact S 6 115 2 (by decide +kernel)
  | exact S 6 115 3 (by decide +kernel)
  | exact S 6 115 4 (by decide +kernel)
  | exact S 6 115 5 (by decide +kernel)
theorem q6_116:ThresholdAt 6 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 116 0 (by decide +kernel)
  | exact S 6 116 1 (by decide +kernel)
  | exact S 6 116 2 (by decide +kernel)
  | exact S 6 116 3 (by decide +kernel)
  | exact S 6 116 4 (by decide +kernel)
  | exact S 6 116 5 (by decide +kernel)
theorem q6_117:ThresholdAt 6 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 117 0 (by decide +kernel)
  | exact S 6 117 1 (by decide +kernel)
  | exact S 6 117 2 (by decide +kernel)
  | exact S 6 117 3 (by decide +kernel)
  | exact S 6 117 4 (by decide +kernel)
  | exact S 6 117 5 (by decide +kernel)
theorem q6_118:ThresholdAt 6 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 118 0 (by decide +kernel)
  | exact S 6 118 1 (by decide +kernel)
  | exact S 6 118 2 (by decide +kernel)
  | exact S 6 118 3 (by decide +kernel)
  | exact S 6 118 4 (by decide +kernel)
  | exact S 6 118 5 (by decide +kernel)
theorem q6_119:ThresholdAt 6 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 119 0 (by decide +kernel)
  | exact S 6 119 1 (by decide +kernel)
  | exact S 6 119 2 (by decide +kernel)
  | exact S 6 119 3 (by decide +kernel)
  | exact S 6 119 4 (by decide +kernel)
  | exact S 6 119 5 (by decide +kernel)
theorem q6_120:ThresholdAt 6 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 120 0 (by decide +kernel)
  | exact S 6 120 1 (by decide +kernel)
  | exact S 6 120 2 (by decide +kernel)
  | exact S 6 120 3 (by decide +kernel)
  | exact S 6 120 4 (by decide +kernel)
  | exact S 6 120 5 (by decide +kernel)
theorem q6_121:ThresholdAt 6 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 121 0 (by decide +kernel)
  | exact S 6 121 1 (by decide +kernel)
  | exact S 6 121 2 (by decide +kernel)
  | exact S 6 121 3 (by decide +kernel)
  | exact S 6 121 4 (by decide +kernel)
  | exact S 6 121 5 (by decide +kernel)
theorem q6_122:ThresholdAt 6 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 122 0 (by decide +kernel)
  | exact S 6 122 1 (by decide +kernel)
  | exact S 6 122 2 (by decide +kernel)
  | exact S 6 122 3 (by decide +kernel)
  | exact S 6 122 4 (by decide +kernel)
  | exact S 6 122 5 (by decide +kernel)
theorem q6_123:ThresholdAt 6 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 123 0 (by decide +kernel)
  | exact S 6 123 1 (by decide +kernel)
  | exact S 6 123 2 (by decide +kernel)
  | exact S 6 123 3 (by decide +kernel)
  | exact S 6 123 4 (by decide +kernel)
  | exact S 6 123 5 (by decide +kernel)
theorem q6_124:ThresholdAt 6 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 124 0 (by decide +kernel)
  | exact S 6 124 1 (by decide +kernel)
  | exact S 6 124 2 (by decide +kernel)
  | exact S 6 124 3 (by decide +kernel)
  | exact S 6 124 4 (by decide +kernel)
  | exact S 6 124 5 (by decide +kernel)
theorem q6_125:ThresholdAt 6 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 125 0 (by decide +kernel)
  | exact S 6 125 1 (by decide +kernel)
  | exact S 6 125 2 (by decide +kernel)
  | exact S 6 125 3 (by decide +kernel)
  | exact S 6 125 4 (by decide +kernel)
  | exact S 6 125 5 (by decide +kernel)
theorem q6_126:ThresholdAt 6 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 126 0 (by decide +kernel)
  | exact S 6 126 1 (by decide +kernel)
  | exact S 6 126 2 (by decide +kernel)
  | exact S 6 126 3 (by decide +kernel)
  | exact S 6 126 4 (by decide +kernel)
  | exact S 6 126 5 (by decide +kernel)
theorem q6_127:ThresholdAt 6 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 127 0 (by decide +kernel)
  | exact S 6 127 1 (by decide +kernel)
  | exact S 6 127 2 (by decide +kernel)
  | exact S 6 127 3 (by decide +kernel)
  | exact S 6 127 4 (by decide +kernel)
  | exact S 6 127 5 (by decide +kernel)
theorem q6_128:ThresholdAt 6 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 128 0 (by decide +kernel)
  | exact S 6 128 1 (by decide +kernel)
  | exact S 6 128 2 (by decide +kernel)
  | exact S 6 128 3 (by decide +kernel)
  | exact S 6 128 4 (by decide +kernel)
  | exact S 6 128 5 (by decide +kernel)
theorem q6_129:ThresholdAt 6 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 129 0 (by decide +kernel)
  | exact S 6 129 1 (by decide +kernel)
  | exact S 6 129 2 (by decide +kernel)
  | exact S 6 129 3 (by decide +kernel)
  | exact S 6 129 4 (by decide +kernel)
  | exact S 6 129 5 (by decide +kernel)
theorem q6_130:ThresholdAt 6 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 130 0 (by decide +kernel)
  | exact S 6 130 1 (by decide +kernel)
  | exact S 6 130 2 (by decide +kernel)
  | exact S 6 130 3 (by decide +kernel)
  | exact S 6 130 4 (by decide +kernel)
  | exact S 6 130 5 (by decide +kernel)
theorem q6_131:ThresholdAt 6 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 131 0 (by decide +kernel)
  | exact S 6 131 1 (by decide +kernel)
  | exact S 6 131 2 (by decide +kernel)
  | exact S 6 131 3 (by decide +kernel)
  | exact S 6 131 4 (by decide +kernel)
  | exact S 6 131 5 (by decide +kernel)
theorem q6_132:ThresholdAt 6 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 132 0 (by decide +kernel)
  | exact S 6 132 1 (by decide +kernel)
  | exact S 6 132 2 (by decide +kernel)
  | exact S 6 132 3 (by decide +kernel)
  | exact S 6 132 4 (by decide +kernel)
  | exact S 6 132 5 (by decide +kernel)
theorem q6_133:ThresholdAt 6 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 133 0 (by decide +kernel)
  | exact S 6 133 1 (by decide +kernel)
  | exact S 6 133 2 (by decide +kernel)
  | exact S 6 133 3 (by decide +kernel)
  | exact S 6 133 4 (by decide +kernel)
  | exact S 6 133 5 (by decide +kernel)
theorem q6_134:ThresholdAt 6 134:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 134 0 (by decide +kernel)
  | exact S 6 134 1 (by decide +kernel)
  | exact S 6 134 2 (by decide +kernel)
  | exact S 6 134 3 (by decide +kernel)
  | exact S 6 134 4 (by decide +kernel)
  | exact S 6 134 5 (by decide +kernel)
theorem q6_135:ThresholdAt 6 135:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 135 0 (by decide +kernel)
  | exact S 6 135 1 (by decide +kernel)
  | exact S 6 135 2 (by decide +kernel)
  | exact S 6 135 3 (by decide +kernel)
  | exact S 6 135 4 (by decide +kernel)
  | exact S 6 135 5 (by decide +kernel)
theorem q6_136:ThresholdAt 6 136:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 136 0 (by decide +kernel)
  | exact S 6 136 1 (by decide +kernel)
  | exact S 6 136 2 (by decide +kernel)
  | exact S 6 136 3 (by decide +kernel)
  | exact S 6 136 4 (by decide +kernel)
  | exact S 6 136 5 (by decide +kernel)
theorem checkedR6:∀ V ∈ List.range 137,ThresholdAt 6 V:=by
  intro V hV
  have hv:V < 137:=List.mem_range.mp hV
  by_cases h0_137:V < 68
  · by_cases h0_68:V < 34
    · by_cases h0_34:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q6_0
              · have he:V = 1:=by omega
                subst V
                exact q6_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q6_2
              · have he:V = 3:=by omega
                subst V
                exact q6_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q6_4
              · have he:V = 5:=by omega
                subst V
                exact q6_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q6_6
              · have he:V = 7:=by omega
                subst V
                exact q6_7
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q6_8
              · have he:V = 9:=by omega
                subst V
                exact q6_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q6_10
              · have he:V = 11:=by omega
                subst V
                exact q6_11
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q6_12
              · have he:V = 13:=by omega
                subst V
                exact q6_13
            · by_cases h14_17:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q6_14
              · by_cases h15_17:V < 16
                · have he:V = 15:=by omega
                  subst V
                  exact q6_15
                · have he:V = 16:=by omega
                  subst V
                  exact q6_16
      · by_cases h17_34:V < 25
        · by_cases h17_25:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q6_17
              · have he:V = 18:=by omega
                subst V
                exact q6_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q6_19
              · have he:V = 20:=by omega
                subst V
                exact q6_20
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q6_21
              · have he:V = 22:=by omega
                subst V
                exact q6_22
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q6_23
              · have he:V = 24:=by omega
                subst V
                exact q6_24
        · by_cases h25_34:V < 29
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q6_25
              · have he:V = 26:=by omega
                subst V
                exact q6_26
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q6_27
              · have he:V = 28:=by omega
                subst V
                exact q6_28
          · by_cases h29_34:V < 31
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q6_29
              · have he:V = 30:=by omega
                subst V
                exact q6_30
            · by_cases h31_34:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q6_31
              · by_cases h32_34:V < 33
                · have he:V = 32:=by omega
                  subst V
                  exact q6_32
                · have he:V = 33:=by omega
                  subst V
                  exact q6_33
    · by_cases h34_68:V < 51
      · by_cases h34_51:V < 42
        · by_cases h34_42:V < 38
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q6_34
              · have he:V = 35:=by omega
                subst V
                exact q6_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q6_36
              · have he:V = 37:=by omega
                subst V
                exact q6_37
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q6_38
              · have he:V = 39:=by omega
                subst V
                exact q6_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q6_40
              · have he:V = 41:=by omega
                subst V
                exact q6_41
        · by_cases h42_51:V < 46
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q6_42
              · have he:V = 43:=by omega
                subst V
                exact q6_43
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q6_44
              · have he:V = 45:=by omega
                subst V
                exact q6_45
          · by_cases h46_51:V < 48
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q6_46
              · have he:V = 47:=by omega
                subst V
                exact q6_47
            · by_cases h48_51:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q6_48
              · by_cases h49_51:V < 50
                · have he:V = 49:=by omega
                  subst V
                  exact q6_49
                · have he:V = 50:=by omega
                  subst V
                  exact q6_50
      · by_cases h51_68:V < 59
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q6_51
              · have he:V = 52:=by omega
                subst V
                exact q6_52
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q6_53
              · have he:V = 54:=by omega
                subst V
                exact q6_54
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q6_55
              · have he:V = 56:=by omega
                subst V
                exact q6_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q6_57
              · have he:V = 58:=by omega
                subst V
                exact q6_58
        · by_cases h59_68:V < 63
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q6_59
              · have he:V = 60:=by omega
                subst V
                exact q6_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q6_61
              · have he:V = 62:=by omega
                subst V
                exact q6_62
          · by_cases h63_68:V < 65
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q6_63
              · have he:V = 64:=by omega
                subst V
                exact q6_64
            · by_cases h65_68:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q6_65
              · by_cases h66_68:V < 67
                · have he:V = 66:=by omega
                  subst V
                  exact q6_66
                · have he:V = 67:=by omega
                  subst V
                  exact q6_67
  · by_cases h68_137:V < 102
    · by_cases h68_102:V < 85
      · by_cases h68_85:V < 76
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q6_68
              · have he:V = 69:=by omega
                subst V
                exact q6_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q6_70
              · have he:V = 71:=by omega
                subst V
                exact q6_71
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q6_72
              · have he:V = 73:=by omega
                subst V
                exact q6_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q6_74
              · have he:V = 75:=by omega
                subst V
                exact q6_75
        · by_cases h76_85:V < 80
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q6_76
              · have he:V = 77:=by omega
                subst V
                exact q6_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q6_78
              · have he:V = 79:=by omega
                subst V
                exact q6_79
          · by_cases h80_85:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q6_80
              · have he:V = 81:=by omega
                subst V
                exact q6_81
            · by_cases h82_85:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q6_82
              · by_cases h83_85:V < 84
                · have he:V = 83:=by omega
                  subst V
                  exact q6_83
                · have he:V = 84:=by omega
                  subst V
                  exact q6_84
      · by_cases h85_102:V < 93
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q6_85
              · have he:V = 86:=by omega
                subst V
                exact q6_86
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q6_87
              · have he:V = 88:=by omega
                subst V
                exact q6_88
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q6_89
              · have he:V = 90:=by omega
                subst V
                exact q6_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q6_91
              · have he:V = 92:=by omega
                subst V
                exact q6_92
        · by_cases h93_102:V < 97
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q6_93
              · have he:V = 94:=by omega
                subst V
                exact q6_94
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q6_95
              · have he:V = 96:=by omega
                subst V
                exact q6_96
          · by_cases h97_102:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q6_97
              · have he:V = 98:=by omega
                subst V
                exact q6_98
            · by_cases h99_102:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q6_99
              · by_cases h100_102:V < 101
                · have he:V = 100:=by omega
                  subst V
                  exact q6_100
                · have he:V = 101:=by omega
                  subst V
                  exact q6_101
    · by_cases h102_137:V < 119
      · by_cases h102_119:V < 110
        · by_cases h102_110:V < 106
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q6_102
              · have he:V = 103:=by omega
                subst V
                exact q6_103
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q6_104
              · have he:V = 105:=by omega
                subst V
                exact q6_105
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q6_106
              · have he:V = 107:=by omega
                subst V
                exact q6_107
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q6_108
              · have he:V = 109:=by omega
                subst V
                exact q6_109
        · by_cases h110_119:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q6_110
              · have he:V = 111:=by omega
                subst V
                exact q6_111
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q6_112
              · have he:V = 113:=by omega
                subst V
                exact q6_113
          · by_cases h114_119:V < 116
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q6_114
              · have he:V = 115:=by omega
                subst V
                exact q6_115
            · by_cases h116_119:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q6_116
              · by_cases h117_119:V < 118
                · have he:V = 117:=by omega
                  subst V
                  exact q6_117
                · have he:V = 118:=by omega
                  subst V
                  exact q6_118
      · by_cases h119_137:V < 128
        · by_cases h119_128:V < 123
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q6_119
              · have he:V = 120:=by omega
                subst V
                exact q6_120
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q6_121
              · have he:V = 122:=by omega
                subst V
                exact q6_122
          · by_cases h123_128:V < 125
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q6_123
              · have he:V = 124:=by omega
                subst V
                exact q6_124
            · by_cases h125_128:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q6_125
              · by_cases h126_128:V < 127
                · have he:V = 126:=by omega
                  subst V
                  exact q6_126
                · have he:V = 127:=by omega
                  subst V
                  exact q6_127
        · by_cases h128_137:V < 132
          · by_cases h128_132:V < 130
            · by_cases h128_130:V < 129
              · have he:V = 128:=by omega
                subst V
                exact q6_128
              · have he:V = 129:=by omega
                subst V
                exact q6_129
            · by_cases h130_132:V < 131
              · have he:V = 130:=by omega
                subst V
                exact q6_130
              · have he:V = 131:=by omega
                subst V
                exact q6_131
          · by_cases h132_137:V < 134
            · by_cases h132_134:V < 133
              · have he:V = 132:=by omega
                subst V
                exact q6_132
              · have he:V = 133:=by omega
                subst V
                exact q6_133
            · by_cases h134_137:V < 135
              · have he:V = 134:=by omega
                subst V
                exact q6_134
              · by_cases h135_137:V < 136
                · have he:V = 135:=by omega
                  subst V
                  exact q6_135
                · have he:V = 136:=by omega
                  subst V
                  exact q6_136
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
