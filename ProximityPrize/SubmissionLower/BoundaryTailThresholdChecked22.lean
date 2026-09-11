import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked21

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q22_0:ThresholdAt 22 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 0 0 (by decide +kernel)
  | exact S 22 0 1 (by decide +kernel)
  | exact S 22 0 2 (by decide +kernel)
  | exact S 22 0 3 (by decide +kernel)
  | exact S 22 0 4 (by decide +kernel)
  | exact S 22 0 5 (by decide +kernel)
theorem q22_1:ThresholdAt 22 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 1 0 (by decide +kernel)
  | exact S 22 1 1 (by decide +kernel)
  | exact S 22 1 2 (by decide +kernel)
  | exact S 22 1 3 (by decide +kernel)
  | exact S 22 1 4 (by decide +kernel)
  | exact S 22 1 5 (by decide +kernel)
theorem q22_2:ThresholdAt 22 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 2 0 (by decide +kernel)
  | exact S 22 2 1 (by decide +kernel)
  | exact S 22 2 2 (by decide +kernel)
  | exact S 22 2 3 (by decide +kernel)
  | exact S 22 2 4 (by decide +kernel)
  | exact S 22 2 5 (by decide +kernel)
theorem q22_3:ThresholdAt 22 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 3 0 (by decide +kernel)
  | exact S 22 3 1 (by decide +kernel)
  | exact S 22 3 2 (by decide +kernel)
  | exact S 22 3 3 (by decide +kernel)
  | exact S 22 3 4 (by decide +kernel)
  | exact S 22 3 5 (by decide +kernel)
theorem q22_4:ThresholdAt 22 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 4 0 (by decide +kernel)
  | exact S 22 4 1 (by decide +kernel)
  | exact S 22 4 2 (by decide +kernel)
  | exact S 22 4 3 (by decide +kernel)
  | exact S 22 4 4 (by decide +kernel)
  | exact S 22 4 5 (by decide +kernel)
theorem q22_5:ThresholdAt 22 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 5 0 (by decide +kernel)
  | exact S 22 5 1 (by decide +kernel)
  | exact S 22 5 2 (by decide +kernel)
  | exact S 22 5 3 (by decide +kernel)
  | exact S 22 5 4 (by decide +kernel)
  | exact S 22 5 5 (by decide +kernel)
theorem q22_6:ThresholdAt 22 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 6 0 (by decide +kernel)
  | exact S 22 6 1 (by decide +kernel)
  | exact S 22 6 2 (by decide +kernel)
  | exact S 22 6 3 (by decide +kernel)
  | exact S 22 6 4 (by decide +kernel)
  | exact S 22 6 5 (by decide +kernel)
theorem q22_7:ThresholdAt 22 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 7 0 (by decide +kernel)
  | exact S 22 7 1 (by decide +kernel)
  | exact S 22 7 2 (by decide +kernel)
  | exact S 22 7 3 (by decide +kernel)
  | exact S 22 7 4 (by decide +kernel)
  | exact S 22 7 5 (by decide +kernel)
theorem q22_8:ThresholdAt 22 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 8 0 (by decide +kernel)
  | exact S 22 8 1 (by decide +kernel)
  | exact S 22 8 2 (by decide +kernel)
  | exact S 22 8 3 (by decide +kernel)
  | exact S 22 8 4 (by decide +kernel)
  | exact S 22 8 5 (by decide +kernel)
theorem q22_9:ThresholdAt 22 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 9 0 (by decide +kernel)
  | exact S 22 9 1 (by decide +kernel)
  | exact S 22 9 2 (by decide +kernel)
  | exact S 22 9 3 (by decide +kernel)
  | exact S 22 9 4 (by decide +kernel)
  | exact S 22 9 5 (by decide +kernel)
theorem q22_10:ThresholdAt 22 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 10 0 (by decide +kernel)
  | exact S 22 10 1 (by decide +kernel)
  | exact S 22 10 2 (by decide +kernel)
  | exact S 22 10 3 (by decide +kernel)
  | exact S 22 10 4 (by decide +kernel)
  | exact S 22 10 5 (by decide +kernel)
theorem q22_11:ThresholdAt 22 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 11 0 (by decide +kernel)
  | exact S 22 11 1 (by decide +kernel)
  | exact S 22 11 2 (by decide +kernel)
  | exact S 22 11 3 (by decide +kernel)
  | exact S 22 11 4 (by decide +kernel)
  | exact S 22 11 5 (by decide +kernel)
theorem q22_12:ThresholdAt 22 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 12 0 (by decide +kernel)
  | exact S 22 12 1 (by decide +kernel)
  | exact S 22 12 2 (by decide +kernel)
  | exact S 22 12 3 (by decide +kernel)
  | exact S 22 12 4 (by decide +kernel)
  | exact S 22 12 5 (by decide +kernel)
theorem q22_13:ThresholdAt 22 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 13 0 (by decide +kernel)
  | exact S 22 13 1 (by decide +kernel)
  | exact S 22 13 2 (by decide +kernel)
  | exact S 22 13 3 (by decide +kernel)
  | exact S 22 13 4 (by decide +kernel)
  | exact S 22 13 5 (by decide +kernel)
theorem q22_14:ThresholdAt 22 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 14 0 (by decide +kernel)
  | exact S 22 14 1 (by decide +kernel)
  | exact S 22 14 2 (by decide +kernel)
  | exact S 22 14 3 (by decide +kernel)
  | exact S 22 14 4 (by decide +kernel)
  | exact S 22 14 5 (by decide +kernel)
theorem q22_15:ThresholdAt 22 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 15 0 (by decide +kernel)
  | exact S 22 15 1 (by decide +kernel)
  | exact S 22 15 2 (by decide +kernel)
  | exact S 22 15 3 (by decide +kernel)
  | exact S 22 15 4 (by decide +kernel)
  | exact S 22 15 5 (by decide +kernel)
theorem q22_16:ThresholdAt 22 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 16 0 (by decide +kernel)
  | exact S 22 16 1 (by decide +kernel)
  | exact S 22 16 2 (by decide +kernel)
  | exact S 22 16 3 (by decide +kernel)
  | exact S 22 16 4 (by decide +kernel)
  | exact S 22 16 5 (by decide +kernel)
theorem q22_17:ThresholdAt 22 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 17 0 (by decide +kernel)
  | exact S 22 17 1 (by decide +kernel)
  | exact S 22 17 2 (by decide +kernel)
  | exact S 22 17 3 (by decide +kernel)
  | exact S 22 17 4 (by decide +kernel)
  | exact S 22 17 5 (by decide +kernel)
theorem q22_18:ThresholdAt 22 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 18 0 (by decide +kernel)
  | exact S 22 18 1 (by decide +kernel)
  | exact S 22 18 2 (by decide +kernel)
  | exact S 22 18 3 (by decide +kernel)
  | exact S 22 18 4 (by decide +kernel)
  | exact S 22 18 5 (by decide +kernel)
theorem q22_19:ThresholdAt 22 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 19 0 (by decide +kernel)
  | exact S 22 19 1 (by decide +kernel)
  | exact S 22 19 2 (by decide +kernel)
  | exact S 22 19 3 (by decide +kernel)
  | exact S 22 19 4 (by decide +kernel)
  | exact S 22 19 5 (by decide +kernel)
theorem q22_20:ThresholdAt 22 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 20 0 (by decide +kernel)
  | exact S 22 20 1 (by decide +kernel)
  | exact S 22 20 2 (by decide +kernel)
  | exact S 22 20 3 (by decide +kernel)
  | exact S 22 20 4 (by decide +kernel)
  | exact S 22 20 5 (by decide +kernel)
theorem q22_21:ThresholdAt 22 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 21 0 (by decide +kernel)
  | exact S 22 21 1 (by decide +kernel)
  | exact S 22 21 2 (by decide +kernel)
  | exact S 22 21 3 (by decide +kernel)
  | exact S 22 21 4 (by decide +kernel)
  | exact S 22 21 5 (by decide +kernel)
theorem q22_22:ThresholdAt 22 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 22 0 (by decide +kernel)
  | exact S 22 22 1 (by decide +kernel)
  | exact S 22 22 2 (by decide +kernel)
  | exact S 22 22 3 (by decide +kernel)
  | exact S 22 22 4 (by decide +kernel)
  | exact S 22 22 5 (by decide +kernel)
theorem q22_23:ThresholdAt 22 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 23 0 (by decide +kernel)
  | exact S 22 23 1 (by decide +kernel)
  | exact S 22 23 2 (by decide +kernel)
  | exact S 22 23 3 (by decide +kernel)
  | exact S 22 23 4 (by decide +kernel)
  | exact S 22 23 5 (by decide +kernel)
theorem q22_24:ThresholdAt 22 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 24 0 (by decide +kernel)
  | exact S 22 24 1 (by decide +kernel)
  | exact S 22 24 2 (by decide +kernel)
  | exact S 22 24 3 (by decide +kernel)
  | exact S 22 24 4 (by decide +kernel)
  | exact S 22 24 5 (by decide +kernel)
theorem q22_25:ThresholdAt 22 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 25 0 (by decide +kernel)
  | exact S 22 25 1 (by decide +kernel)
  | exact S 22 25 2 (by decide +kernel)
  | exact S 22 25 3 (by decide +kernel)
  | exact S 22 25 4 (by decide +kernel)
  | exact S 22 25 5 (by decide +kernel)
theorem q22_26:ThresholdAt 22 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 26 0 (by decide +kernel)
  | exact S 22 26 1 (by decide +kernel)
  | exact S 22 26 2 (by decide +kernel)
  | exact S 22 26 3 (by decide +kernel)
  | exact S 22 26 4 (by decide +kernel)
  | exact S 22 26 5 (by decide +kernel)
theorem q22_27:ThresholdAt 22 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 27 0 (by decide +kernel)
  | exact S 22 27 1 (by decide +kernel)
  | exact S 22 27 2 (by decide +kernel)
  | exact S 22 27 3 (by decide +kernel)
  | exact S 22 27 4 (by decide +kernel)
  | exact S 22 27 5 (by decide +kernel)
theorem q22_28:ThresholdAt 22 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 28 0 (by decide +kernel)
  | exact S 22 28 1 (by decide +kernel)
  | exact S 22 28 2 (by decide +kernel)
  | exact S 22 28 3 (by decide +kernel)
  | exact S 22 28 4 (by decide +kernel)
  | exact S 22 28 5 (by decide +kernel)
theorem q22_29:ThresholdAt 22 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 29 0 (by decide +kernel)
  | exact S 22 29 1 (by decide +kernel)
  | exact S 22 29 2 (by decide +kernel)
  | exact S 22 29 3 (by decide +kernel)
  | exact S 22 29 4 (by decide +kernel)
  | exact S 22 29 5 (by decide +kernel)
theorem q22_30:ThresholdAt 22 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 30 0 (by decide +kernel)
  | exact S 22 30 1 (by decide +kernel)
  | exact S 22 30 2 (by decide +kernel)
  | exact S 22 30 3 (by decide +kernel)
  | exact S 22 30 4 (by decide +kernel)
  | exact S 22 30 5 (by decide +kernel)
theorem q22_31:ThresholdAt 22 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 31 0 (by decide +kernel)
  | exact S 22 31 1 (by decide +kernel)
  | exact S 22 31 2 (by decide +kernel)
  | exact S 22 31 3 (by decide +kernel)
  | exact S 22 31 4 (by decide +kernel)
  | exact S 22 31 5 (by decide +kernel)
theorem q22_32:ThresholdAt 22 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 32 0 (by decide +kernel)
  | exact S 22 32 1 (by decide +kernel)
  | exact S 22 32 2 (by decide +kernel)
  | exact S 22 32 3 (by decide +kernel)
  | exact S 22 32 4 (by decide +kernel)
  | exact S 22 32 5 (by decide +kernel)
theorem q22_33:ThresholdAt 22 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 33 0 (by decide +kernel)
  | exact S 22 33 1 (by decide +kernel)
  | exact S 22 33 2 (by decide +kernel)
  | exact S 22 33 3 (by decide +kernel)
  | exact S 22 33 4 (by decide +kernel)
  | exact S 22 33 5 (by decide +kernel)
theorem q22_34:ThresholdAt 22 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 34 0 (by decide +kernel)
  | exact S 22 34 1 (by decide +kernel)
  | exact S 22 34 2 (by decide +kernel)
  | exact S 22 34 3 (by decide +kernel)
  | exact S 22 34 4 (by decide +kernel)
  | exact S 22 34 5 (by decide +kernel)
theorem q22_35:ThresholdAt 22 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 35 0 (by decide +kernel)
  | exact S 22 35 1 (by decide +kernel)
  | exact S 22 35 2 (by decide +kernel)
  | exact S 22 35 3 (by decide +kernel)
  | exact S 22 35 4 (by decide +kernel)
  | exact S 22 35 5 (by decide +kernel)
theorem q22_36:ThresholdAt 22 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 36 0 (by decide +kernel)
  | exact S 22 36 1 (by decide +kernel)
  | exact S 22 36 2 (by decide +kernel)
  | exact S 22 36 3 (by decide +kernel)
  | exact S 22 36 4 (by decide +kernel)
  | exact S 22 36 5 (by decide +kernel)
theorem q22_37:ThresholdAt 22 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 37 0 (by decide +kernel)
  | exact S 22 37 1 (by decide +kernel)
  | exact S 22 37 2 (by decide +kernel)
  | exact S 22 37 3 (by decide +kernel)
  | exact S 22 37 4 (by decide +kernel)
  | exact S 22 37 5 (by decide +kernel)
theorem q22_38:ThresholdAt 22 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 38 0 (by decide +kernel)
  | exact S 22 38 1 (by decide +kernel)
  | exact S 22 38 2 (by decide +kernel)
  | exact S 22 38 3 (by decide +kernel)
  | exact S 22 38 4 (by decide +kernel)
  | exact S 22 38 5 (by decide +kernel)
theorem q22_39:ThresholdAt 22 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 39 0 (by decide +kernel)
  | exact S 22 39 1 (by decide +kernel)
  | exact S 22 39 2 (by decide +kernel)
  | exact S 22 39 3 (by decide +kernel)
  | exact S 22 39 4 (by decide +kernel)
  | exact S 22 39 5 (by decide +kernel)
theorem q22_40:ThresholdAt 22 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 40 0 (by decide +kernel)
  | exact S 22 40 1 (by decide +kernel)
  | exact S 22 40 2 (by decide +kernel)
  | exact S 22 40 3 (by decide +kernel)
  | exact S 22 40 4 (by decide +kernel)
  | exact S 22 40 5 (by decide +kernel)
theorem q22_41:ThresholdAt 22 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 41 0 (by decide +kernel)
  | exact S 22 41 1 (by decide +kernel)
  | exact S 22 41 2 (by decide +kernel)
  | exact S 22 41 3 (by decide +kernel)
  | exact S 22 41 4 (by decide +kernel)
  | exact S 22 41 5 (by decide +kernel)
theorem q22_42:ThresholdAt 22 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 42 0 (by decide +kernel)
  | exact S 22 42 1 (by decide +kernel)
  | exact S 22 42 2 (by decide +kernel)
  | exact S 22 42 3 (by decide +kernel)
  | exact S 22 42 4 (by decide +kernel)
  | exact S 22 42 5 (by decide +kernel)
theorem q22_43:ThresholdAt 22 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 43 0 (by decide +kernel)
  | exact S 22 43 1 (by decide +kernel)
  | exact S 22 43 2 (by decide +kernel)
  | exact S 22 43 3 (by decide +kernel)
  | exact S 22 43 4 (by decide +kernel)
  | exact S 22 43 5 (by decide +kernel)
theorem q22_44:ThresholdAt 22 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 44 0 (by decide +kernel)
  | exact S 22 44 1 (by decide +kernel)
  | exact S 22 44 2 (by decide +kernel)
  | exact S 22 44 3 (by decide +kernel)
  | exact S 22 44 4 (by decide +kernel)
  | exact S 22 44 5 (by decide +kernel)
theorem q22_45:ThresholdAt 22 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 45 0 (by decide +kernel)
  | exact S 22 45 1 (by decide +kernel)
  | exact S 22 45 2 (by decide +kernel)
  | exact S 22 45 3 (by decide +kernel)
  | exact S 22 45 4 (by decide +kernel)
  | exact S 22 45 5 (by decide +kernel)
theorem q22_46:ThresholdAt 22 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 46 0 (by decide +kernel)
  | exact S 22 46 1 (by decide +kernel)
  | exact S 22 46 2 (by decide +kernel)
  | exact S 22 46 3 (by decide +kernel)
  | exact S 22 46 4 (by decide +kernel)
  | exact S 22 46 5 (by decide +kernel)
theorem q22_47:ThresholdAt 22 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 47 0 (by decide +kernel)
  | exact S 22 47 1 (by decide +kernel)
  | exact S 22 47 2 (by decide +kernel)
  | exact S 22 47 3 (by decide +kernel)
  | exact S 22 47 4 (by decide +kernel)
  | exact S 22 47 5 (by decide +kernel)
theorem q22_48:ThresholdAt 22 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 48 0 (by decide +kernel)
  | exact S 22 48 1 (by decide +kernel)
  | exact S 22 48 2 (by decide +kernel)
  | exact S 22 48 3 (by decide +kernel)
  | exact S 22 48 4 (by decide +kernel)
  | exact S 22 48 5 (by decide +kernel)
theorem q22_49:ThresholdAt 22 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 49 0 (by decide +kernel)
  | exact S 22 49 1 (by decide +kernel)
  | exact S 22 49 2 (by decide +kernel)
  | exact S 22 49 3 (by decide +kernel)
  | exact S 22 49 4 (by decide +kernel)
  | exact S 22 49 5 (by decide +kernel)
theorem q22_50:ThresholdAt 22 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 50 0 (by decide +kernel)
  | exact S 22 50 1 (by decide +kernel)
  | exact S 22 50 2 (by decide +kernel)
  | exact S 22 50 3 (by decide +kernel)
  | exact S 22 50 4 (by decide +kernel)
  | exact S 22 50 5 (by decide +kernel)
theorem q22_51:ThresholdAt 22 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 51 0 (by decide +kernel)
  | exact S 22 51 1 (by decide +kernel)
  | exact S 22 51 2 (by decide +kernel)
  | exact S 22 51 3 (by decide +kernel)
  | exact S 22 51 4 (by decide +kernel)
  | exact S 22 51 5 (by decide +kernel)
theorem q22_52:ThresholdAt 22 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 52 0 (by decide +kernel)
  | exact S 22 52 1 (by decide +kernel)
  | exact S 22 52 2 (by decide +kernel)
  | exact S 22 52 3 (by decide +kernel)
  | exact S 22 52 4 (by decide +kernel)
  | exact S 22 52 5 (by decide +kernel)
theorem q22_53:ThresholdAt 22 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 53 0 (by decide +kernel)
  | exact S 22 53 1 (by decide +kernel)
  | exact S 22 53 2 (by decide +kernel)
  | exact S 22 53 3 (by decide +kernel)
  | exact S 22 53 4 (by decide +kernel)
  | exact S 22 53 5 (by decide +kernel)
theorem q22_54:ThresholdAt 22 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 54 0 (by decide +kernel)
  | exact S 22 54 1 (by decide +kernel)
  | exact S 22 54 2 (by decide +kernel)
  | exact S 22 54 3 (by decide +kernel)
  | exact S 22 54 4 (by decide +kernel)
  | exact S 22 54 5 (by decide +kernel)
theorem q22_55:ThresholdAt 22 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 55 0 (by decide +kernel)
  | exact S 22 55 1 (by decide +kernel)
  | exact S 22 55 2 (by decide +kernel)
  | exact S 22 55 3 (by decide +kernel)
  | exact S 22 55 4 (by decide +kernel)
  | exact S 22 55 5 (by decide +kernel)
theorem q22_56:ThresholdAt 22 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 56 0 (by decide +kernel)
  | exact S 22 56 1 (by decide +kernel)
  | exact S 22 56 2 (by decide +kernel)
  | exact S 22 56 3 (by decide +kernel)
  | exact S 22 56 4 (by decide +kernel)
  | exact S 22 56 5 (by decide +kernel)
theorem q22_57:ThresholdAt 22 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 57 0 (by decide +kernel)
  | exact S 22 57 1 (by decide +kernel)
  | exact S 22 57 2 (by decide +kernel)
  | exact S 22 57 3 (by decide +kernel)
  | exact S 22 57 4 (by decide +kernel)
  | exact S 22 57 5 (by decide +kernel)
theorem q22_58:ThresholdAt 22 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 58 0 (by decide +kernel)
  | exact S 22 58 1 (by decide +kernel)
  | exact S 22 58 2 (by decide +kernel)
  | exact S 22 58 3 (by decide +kernel)
  | exact S 22 58 4 (by decide +kernel)
  | exact S 22 58 5 (by decide +kernel)
theorem q22_59:ThresholdAt 22 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 59 0 (by decide +kernel)
  | exact S 22 59 1 (by decide +kernel)
  | exact S 22 59 2 (by decide +kernel)
  | exact S 22 59 3 (by decide +kernel)
  | exact S 22 59 4 (by decide +kernel)
  | exact S 22 59 5 (by decide +kernel)
theorem q22_60:ThresholdAt 22 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 60 0 (by decide +kernel)
  | exact S 22 60 1 (by decide +kernel)
  | exact S 22 60 2 (by decide +kernel)
  | exact S 22 60 3 (by decide +kernel)
  | exact S 22 60 4 (by decide +kernel)
  | exact S 22 60 5 (by decide +kernel)
theorem q22_61:ThresholdAt 22 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 61 0 (by decide +kernel)
  | exact S 22 61 1 (by decide +kernel)
  | exact S 22 61 2 (by decide +kernel)
  | exact S 22 61 3 (by decide +kernel)
  | exact S 22 61 4 (by decide +kernel)
  | exact S 22 61 5 (by decide +kernel)
theorem q22_62:ThresholdAt 22 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 62 0 (by decide +kernel)
  | exact S 22 62 1 (by decide +kernel)
  | exact S 22 62 2 (by decide +kernel)
  | exact S 22 62 3 (by decide +kernel)
  | exact S 22 62 4 (by decide +kernel)
  | exact S 22 62 5 (by decide +kernel)
theorem q22_63:ThresholdAt 22 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 63 0 (by decide +kernel)
  | exact S 22 63 1 (by decide +kernel)
  | exact S 22 63 2 (by decide +kernel)
  | exact S 22 63 3 (by decide +kernel)
  | exact S 22 63 4 (by decide +kernel)
  | exact S 22 63 5 (by decide +kernel)
theorem q22_64:ThresholdAt 22 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 64 0 (by decide +kernel)
  | exact S 22 64 1 (by decide +kernel)
  | exact S 22 64 2 (by decide +kernel)
  | exact S 22 64 3 (by decide +kernel)
  | exact S 22 64 4 (by decide +kernel)
  | exact S 22 64 5 (by decide +kernel)
theorem q22_65:ThresholdAt 22 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 65 0 (by decide +kernel)
  | exact S 22 65 1 (by decide +kernel)
  | exact S 22 65 2 (by decide +kernel)
  | exact S 22 65 3 (by decide +kernel)
  | exact S 22 65 4 (by decide +kernel)
  | exact S 22 65 5 (by decide +kernel)
theorem q22_66:ThresholdAt 22 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 66 0 (by decide +kernel)
  | exact S 22 66 1 (by decide +kernel)
  | exact S 22 66 2 (by decide +kernel)
  | exact S 22 66 3 (by decide +kernel)
  | exact S 22 66 4 (by decide +kernel)
  | exact S 22 66 5 (by decide +kernel)
theorem q22_67:ThresholdAt 22 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 67 0 (by decide +kernel)
  | exact S 22 67 1 (by decide +kernel)
  | exact S 22 67 2 (by decide +kernel)
  | exact S 22 67 3 (by decide +kernel)
  | exact S 22 67 4 (by decide +kernel)
  | exact S 22 67 5 (by decide +kernel)
theorem q22_68:ThresholdAt 22 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 68 0 (by decide +kernel)
  | exact S 22 68 1 (by decide +kernel)
  | exact S 22 68 2 (by decide +kernel)
  | exact S 22 68 3 (by decide +kernel)
  | exact S 22 68 4 (by decide +kernel)
  | exact S 22 68 5 (by decide +kernel)
theorem q22_69:ThresholdAt 22 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 69 0 (by decide +kernel)
  | exact S 22 69 1 (by decide +kernel)
  | exact S 22 69 2 (by decide +kernel)
  | exact S 22 69 3 (by decide +kernel)
  | exact S 22 69 4 (by decide +kernel)
  | exact S 22 69 5 (by decide +kernel)
theorem q22_70:ThresholdAt 22 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 70 0 (by decide +kernel)
  | exact S 22 70 1 (by decide +kernel)
  | exact S 22 70 2 (by decide +kernel)
  | exact S 22 70 3 (by decide +kernel)
  | exact S 22 70 4 (by decide +kernel)
  | exact S 22 70 5 (by decide +kernel)
theorem q22_71:ThresholdAt 22 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 71 0 (by decide +kernel)
  | exact S 22 71 1 (by decide +kernel)
  | exact S 22 71 2 (by decide +kernel)
  | exact S 22 71 3 (by decide +kernel)
  | exact S 22 71 4 (by decide +kernel)
  | exact S 22 71 5 (by decide +kernel)
theorem q22_72:ThresholdAt 22 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 72 0 (by decide +kernel)
  | exact S 22 72 1 (by decide +kernel)
  | exact S 22 72 2 (by decide +kernel)
  | exact S 22 72 3 (by decide +kernel)
  | exact S 22 72 4 (by decide +kernel)
  | exact S 22 72 5 (by decide +kernel)
theorem q22_73:ThresholdAt 22 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 73 0 (by decide +kernel)
  | exact S 22 73 1 (by decide +kernel)
  | exact S 22 73 2 (by decide +kernel)
  | exact S 22 73 3 (by decide +kernel)
  | exact S 22 73 4 (by decide +kernel)
  | exact S 22 73 5 (by decide +kernel)
theorem q22_74:ThresholdAt 22 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 74 0 (by decide +kernel)
  | exact S 22 74 1 (by decide +kernel)
  | exact S 22 74 2 (by decide +kernel)
  | exact S 22 74 3 (by decide +kernel)
  | exact S 22 74 4 (by decide +kernel)
  | exact S 22 74 5 (by decide +kernel)
theorem q22_75:ThresholdAt 22 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 75 0 (by decide +kernel)
  | exact S 22 75 1 (by decide +kernel)
  | exact S 22 75 2 (by decide +kernel)
  | exact S 22 75 3 (by decide +kernel)
  | exact S 22 75 4 (by decide +kernel)
  | exact S 22 75 5 (by decide +kernel)
theorem q22_76:ThresholdAt 22 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 76 0 (by decide +kernel)
  | exact S 22 76 1 (by decide +kernel)
  | exact S 22 76 2 (by decide +kernel)
  | exact S 22 76 3 (by decide +kernel)
  | exact S 22 76 4 (by decide +kernel)
  | exact S 22 76 5 (by decide +kernel)
theorem q22_77:ThresholdAt 22 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 77 0 (by decide +kernel)
  | exact S 22 77 1 (by decide +kernel)
  | exact S 22 77 2 (by decide +kernel)
  | exact S 22 77 3 (by decide +kernel)
  | exact S 22 77 4 (by decide +kernel)
  | exact S 22 77 5 (by decide +kernel)
theorem q22_78:ThresholdAt 22 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 78 0 (by decide +kernel)
  | exact S 22 78 1 (by decide +kernel)
  | exact S 22 78 2 (by decide +kernel)
  | exact S 22 78 3 (by decide +kernel)
  | exact S 22 78 4 (by decide +kernel)
  | exact S 22 78 5 (by decide +kernel)
theorem q22_79:ThresholdAt 22 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 79 0 (by decide +kernel)
  | exact S 22 79 1 (by decide +kernel)
  | exact S 22 79 2 (by decide +kernel)
  | exact S 22 79 3 (by decide +kernel)
  | exact S 22 79 4 (by decide +kernel)
  | exact S 22 79 5 (by decide +kernel)
theorem q22_80:ThresholdAt 22 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 80 0 (by decide +kernel)
  | exact S 22 80 1 (by decide +kernel)
  | exact S 22 80 2 (by decide +kernel)
  | exact S 22 80 3 (by decide +kernel)
  | exact S 22 80 4 (by decide +kernel)
  | exact S 22 80 5 (by decide +kernel)
theorem q22_81:ThresholdAt 22 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 81 0 (by decide +kernel)
  | exact S 22 81 1 (by decide +kernel)
  | exact S 22 81 2 (by decide +kernel)
  | exact S 22 81 3 (by decide +kernel)
  | exact S 22 81 4 (by decide +kernel)
  | exact S 22 81 5 (by decide +kernel)
theorem q22_82:ThresholdAt 22 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 82 0 (by decide +kernel)
  | exact S 22 82 1 (by decide +kernel)
  | exact S 22 82 2 (by decide +kernel)
  | exact S 22 82 3 (by decide +kernel)
  | exact S 22 82 4 (by decide +kernel)
  | exact S 22 82 5 (by decide +kernel)
theorem q22_83:ThresholdAt 22 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 83 0 (by decide +kernel)
  | exact S 22 83 1 (by decide +kernel)
  | exact S 22 83 2 (by decide +kernel)
  | exact S 22 83 3 (by decide +kernel)
  | exact S 22 83 4 (by decide +kernel)
  | exact S 22 83 5 (by decide +kernel)
theorem q22_84:ThresholdAt 22 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 84 0 (by decide +kernel)
  | exact S 22 84 1 (by decide +kernel)
  | exact S 22 84 2 (by decide +kernel)
  | exact S 22 84 3 (by decide +kernel)
  | exact S 22 84 4 (by decide +kernel)
  | exact S 22 84 5 (by decide +kernel)
theorem q22_85:ThresholdAt 22 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 85 0 (by decide +kernel)
  | exact S 22 85 1 (by decide +kernel)
  | exact S 22 85 2 (by decide +kernel)
  | exact S 22 85 3 (by decide +kernel)
  | exact S 22 85 4 (by decide +kernel)
  | exact S 22 85 5 (by decide +kernel)
theorem q22_86:ThresholdAt 22 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 86 0 (by decide +kernel)
  | exact S 22 86 1 (by decide +kernel)
  | exact S 22 86 2 (by decide +kernel)
  | exact S 22 86 3 (by decide +kernel)
  | exact S 22 86 4 (by decide +kernel)
  | exact S 22 86 5 (by decide +kernel)
theorem q22_87:ThresholdAt 22 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 87 0 (by decide +kernel)
  | exact S 22 87 1 (by decide +kernel)
  | exact S 22 87 2 (by decide +kernel)
  | exact S 22 87 3 (by decide +kernel)
  | exact S 22 87 4 (by decide +kernel)
  | exact S 22 87 5 (by decide +kernel)
theorem q22_88:ThresholdAt 22 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 88 0 (by decide +kernel)
  | exact S 22 88 1 (by decide +kernel)
  | exact S 22 88 2 (by decide +kernel)
  | exact S 22 88 3 (by decide +kernel)
  | exact S 22 88 4 (by decide +kernel)
  | exact S 22 88 5 (by decide +kernel)
theorem q22_89:ThresholdAt 22 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 89 0 (by decide +kernel)
  | exact S 22 89 1 (by decide +kernel)
  | exact S 22 89 2 (by decide +kernel)
  | exact S 22 89 3 (by decide +kernel)
  | exact S 22 89 4 (by decide +kernel)
  | exact S 22 89 5 (by decide +kernel)
theorem q22_90:ThresholdAt 22 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 90 0 (by decide +kernel)
  | exact S 22 90 1 (by decide +kernel)
  | exact S 22 90 2 (by decide +kernel)
  | exact S 22 90 3 (by decide +kernel)
  | exact S 22 90 4 (by decide +kernel)
  | exact S 22 90 5 (by decide +kernel)
theorem q22_91:ThresholdAt 22 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 91 0 (by decide +kernel)
  | exact S 22 91 1 (by decide +kernel)
  | exact S 22 91 2 (by decide +kernel)
  | exact S 22 91 3 (by decide +kernel)
  | exact S 22 91 4 (by decide +kernel)
  | exact S 22 91 5 (by decide +kernel)
theorem q22_92:ThresholdAt 22 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 92 0 (by decide +kernel)
  | exact S 22 92 1 (by decide +kernel)
  | exact S 22 92 2 (by decide +kernel)
  | exact S 22 92 3 (by decide +kernel)
  | exact S 22 92 4 (by decide +kernel)
  | exact S 22 92 5 (by decide +kernel)
theorem q22_93:ThresholdAt 22 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 93 0 (by decide +kernel)
  | exact S 22 93 1 (by decide +kernel)
  | exact S 22 93 2 (by decide +kernel)
  | exact S 22 93 3 (by decide +kernel)
  | exact S 22 93 4 (by decide +kernel)
  | exact S 22 93 5 (by decide +kernel)
theorem q22_94:ThresholdAt 22 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 94 0 (by decide +kernel)
  | exact S 22 94 1 (by decide +kernel)
  | exact S 22 94 2 (by decide +kernel)
  | exact S 22 94 3 (by decide +kernel)
  | exact S 22 94 4 (by decide +kernel)
  | exact S 22 94 5 (by decide +kernel)
theorem q22_95:ThresholdAt 22 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 95 0 (by decide +kernel)
  | exact S 22 95 1 (by decide +kernel)
  | exact S 22 95 2 (by decide +kernel)
  | exact S 22 95 3 (by decide +kernel)
  | exact S 22 95 4 (by decide +kernel)
  | exact S 22 95 5 (by decide +kernel)
theorem q22_96:ThresholdAt 22 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 96 0 (by decide +kernel)
  | exact S 22 96 1 (by decide +kernel)
  | exact S 22 96 2 (by decide +kernel)
  | exact S 22 96 3 (by decide +kernel)
  | exact S 22 96 4 (by decide +kernel)
  | exact S 22 96 5 (by decide +kernel)
theorem q22_97:ThresholdAt 22 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 97 0 (by decide +kernel)
  | exact S 22 97 1 (by decide +kernel)
  | exact S 22 97 2 (by decide +kernel)
  | exact S 22 97 3 (by decide +kernel)
  | exact S 22 97 4 (by decide +kernel)
  | exact S 22 97 5 (by decide +kernel)
theorem q22_98:ThresholdAt 22 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 98 0 (by decide +kernel)
  | exact S 22 98 1 (by decide +kernel)
  | exact S 22 98 2 (by decide +kernel)
  | exact S 22 98 3 (by decide +kernel)
  | exact S 22 98 4 (by decide +kernel)
  | exact S 22 98 5 (by decide +kernel)
theorem q22_99:ThresholdAt 22 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 99 0 (by decide +kernel)
  | exact S 22 99 1 (by decide +kernel)
  | exact S 22 99 2 (by decide +kernel)
  | exact S 22 99 3 (by decide +kernel)
  | exact S 22 99 4 (by decide +kernel)
  | exact S 22 99 5 (by decide +kernel)
theorem q22_100:ThresholdAt 22 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 100 0 (by decide +kernel)
  | exact S 22 100 1 (by decide +kernel)
  | exact S 22 100 2 (by decide +kernel)
  | exact S 22 100 3 (by decide +kernel)
  | exact S 22 100 4 (by decide +kernel)
  | exact S 22 100 5 (by decide +kernel)
theorem q22_101:ThresholdAt 22 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 101 0 (by decide +kernel)
  | exact S 22 101 1 (by decide +kernel)
  | exact S 22 101 2 (by decide +kernel)
  | exact S 22 101 3 (by decide +kernel)
  | exact S 22 101 4 (by decide +kernel)
  | exact S 22 101 5 (by decide +kernel)
theorem q22_102:ThresholdAt 22 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 102 0 (by decide +kernel)
  | exact S 22 102 1 (by decide +kernel)
  | exact S 22 102 2 (by decide +kernel)
  | exact S 22 102 3 (by decide +kernel)
  | exact S 22 102 4 (by decide +kernel)
  | exact S 22 102 5 (by decide +kernel)
theorem q22_103:ThresholdAt 22 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 103 0 (by decide +kernel)
  | exact S 22 103 1 (by decide +kernel)
  | exact S 22 103 2 (by decide +kernel)
  | exact S 22 103 3 (by decide +kernel)
  | exact S 22 103 4 (by decide +kernel)
  | exact S 22 103 5 (by decide +kernel)
theorem q22_104:ThresholdAt 22 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 104 0 (by decide +kernel)
  | exact S 22 104 1 (by decide +kernel)
  | exact S 22 104 2 (by decide +kernel)
  | exact S 22 104 3 (by decide +kernel)
  | exact S 22 104 4 (by decide +kernel)
  | exact S 22 104 5 (by decide +kernel)
theorem q22_105:ThresholdAt 22 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 105 0 (by decide +kernel)
  | exact S 22 105 1 (by decide +kernel)
  | exact S 22 105 2 (by decide +kernel)
  | exact S 22 105 3 (by decide +kernel)
  | exact S 22 105 4 (by decide +kernel)
  | exact S 22 105 5 (by decide +kernel)
theorem q22_106:ThresholdAt 22 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 106 0 (by decide +kernel)
  | exact S 22 106 1 (by decide +kernel)
  | exact S 22 106 2 (by decide +kernel)
  | exact S 22 106 3 (by decide +kernel)
  | exact S 22 106 4 (by decide +kernel)
  | exact S 22 106 5 (by decide +kernel)
theorem q22_107:ThresholdAt 22 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 107 0 (by decide +kernel)
  | exact S 22 107 1 (by decide +kernel)
  | exact S 22 107 2 (by decide +kernel)
  | exact S 22 107 3 (by decide +kernel)
  | exact S 22 107 4 (by decide +kernel)
  | exact S 22 107 5 (by decide +kernel)
theorem q22_108:ThresholdAt 22 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 108 0 (by decide +kernel)
  | exact S 22 108 1 (by decide +kernel)
  | exact S 22 108 2 (by decide +kernel)
  | exact S 22 108 3 (by decide +kernel)
  | exact S 22 108 4 (by decide +kernel)
  | exact S 22 108 5 (by decide +kernel)
theorem q22_109:ThresholdAt 22 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 109 0 (by decide +kernel)
  | exact S 22 109 1 (by decide +kernel)
  | exact S 22 109 2 (by decide +kernel)
  | exact S 22 109 3 (by decide +kernel)
  | exact S 22 109 4 (by decide +kernel)
  | exact S 22 109 5 (by decide +kernel)
theorem q22_110:ThresholdAt 22 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 110 0 (by decide +kernel)
  | exact S 22 110 1 (by decide +kernel)
  | exact S 22 110 2 (by decide +kernel)
  | exact S 22 110 3 (by decide +kernel)
  | exact S 22 110 4 (by decide +kernel)
  | exact S 22 110 5 (by decide +kernel)
theorem q22_111:ThresholdAt 22 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 111 0 (by decide +kernel)
  | exact S 22 111 1 (by decide +kernel)
  | exact S 22 111 2 (by decide +kernel)
  | exact S 22 111 3 (by decide +kernel)
  | exact S 22 111 4 (by decide +kernel)
  | exact S 22 111 5 (by decide +kernel)
theorem q22_112:ThresholdAt 22 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 112 0 (by decide +kernel)
  | exact S 22 112 1 (by decide +kernel)
  | exact S 22 112 2 (by decide +kernel)
  | exact S 22 112 3 (by decide +kernel)
  | exact S 22 112 4 (by decide +kernel)
  | exact S 22 112 5 (by decide +kernel)
theorem q22_113:ThresholdAt 22 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 113 0 (by decide +kernel)
  | exact S 22 113 1 (by decide +kernel)
  | exact S 22 113 2 (by decide +kernel)
  | exact S 22 113 3 (by decide +kernel)
  | exact S 22 113 4 (by decide +kernel)
  | exact S 22 113 5 (by decide +kernel)
theorem q22_114:ThresholdAt 22 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 114 0 (by decide +kernel)
  | exact S 22 114 1 (by decide +kernel)
  | exact S 22 114 2 (by decide +kernel)
  | exact S 22 114 3 (by decide +kernel)
  | exact S 22 114 4 (by decide +kernel)
  | exact S 22 114 5 (by decide +kernel)
theorem q22_115:ThresholdAt 22 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 115 0 (by decide +kernel)
  | exact S 22 115 1 (by decide +kernel)
  | exact S 22 115 2 (by decide +kernel)
  | exact S 22 115 3 (by decide +kernel)
  | exact S 22 115 4 (by decide +kernel)
  | exact S 22 115 5 (by decide +kernel)
theorem q22_116:ThresholdAt 22 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 116 0 (by decide +kernel)
  | exact S 22 116 1 (by decide +kernel)
  | exact S 22 116 2 (by decide +kernel)
  | exact S 22 116 3 (by decide +kernel)
  | exact S 22 116 4 (by decide +kernel)
  | exact S 22 116 5 (by decide +kernel)
theorem q22_117:ThresholdAt 22 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 117 0 (by decide +kernel)
  | exact S 22 117 1 (by decide +kernel)
  | exact S 22 117 2 (by decide +kernel)
  | exact S 22 117 3 (by decide +kernel)
  | exact S 22 117 4 (by decide +kernel)
  | exact S 22 117 5 (by decide +kernel)
theorem q22_118:ThresholdAt 22 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 118 0 (by decide +kernel)
  | exact S 22 118 1 (by decide +kernel)
  | exact S 22 118 2 (by decide +kernel)
  | exact S 22 118 3 (by decide +kernel)
  | exact S 22 118 4 (by decide +kernel)
  | exact S 22 118 5 (by decide +kernel)
theorem q22_119:ThresholdAt 22 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 119 0 (by decide +kernel)
  | exact S 22 119 1 (by decide +kernel)
  | exact S 22 119 2 (by decide +kernel)
  | exact S 22 119 3 (by decide +kernel)
  | exact S 22 119 4 (by decide +kernel)
  | exact S 22 119 5 (by decide +kernel)
theorem q22_120:ThresholdAt 22 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 120 0 (by decide +kernel)
  | exact S 22 120 1 (by decide +kernel)
  | exact S 22 120 2 (by decide +kernel)
  | exact S 22 120 3 (by decide +kernel)
  | exact S 22 120 4 (by decide +kernel)
  | exact S 22 120 5 (by decide +kernel)
theorem checkedR22:∀ V ∈ List.range 121,ThresholdAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0_121:V < 60
  · by_cases h0_60:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q22_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q22_1
              · have he:V = 2:=by omega
                subst V
                exact q22_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q22_3
              · have he:V = 4:=by omega
                subst V
                exact q22_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q22_5
              · have he:V = 6:=by omega
                subst V
                exact q22_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q22_7
              · have he:V = 8:=by omega
                subst V
                exact q22_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q22_9
              · have he:V = 10:=by omega
                subst V
                exact q22_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q22_11
              · have he:V = 12:=by omega
                subst V
                exact q22_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q22_13
              · have he:V = 14:=by omega
                subst V
                exact q22_14
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have he:V = 15:=by omega
              subst V
              exact q22_15
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q22_16
              · have he:V = 17:=by omega
                subst V
                exact q22_17
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q22_18
              · have he:V = 19:=by omega
                subst V
                exact q22_19
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q22_20
              · have he:V = 21:=by omega
                subst V
                exact q22_21
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q22_22
              · have he:V = 23:=by omega
                subst V
                exact q22_23
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q22_24
              · have he:V = 25:=by omega
                subst V
                exact q22_25
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q22_26
              · have he:V = 27:=by omega
                subst V
                exact q22_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q22_28
              · have he:V = 29:=by omega
                subst V
                exact q22_29
    · by_cases h30_60:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have he:V = 30:=by omega
              subst V
              exact q22_30
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q22_31
              · have he:V = 32:=by omega
                subst V
                exact q22_32
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q22_33
              · have he:V = 34:=by omega
                subst V
                exact q22_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q22_35
              · have he:V = 36:=by omega
                subst V
                exact q22_36
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q22_37
              · have he:V = 38:=by omega
                subst V
                exact q22_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q22_39
              · have he:V = 40:=by omega
                subst V
                exact q22_40
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q22_41
              · have he:V = 42:=by omega
                subst V
                exact q22_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q22_43
              · have he:V = 44:=by omega
                subst V
                exact q22_44
      · by_cases h45_60:V < 52
        · by_cases h45_52:V < 48
          · by_cases h45_48:V < 46
            · have he:V = 45:=by omega
              subst V
              exact q22_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q22_46
              · have he:V = 47:=by omega
                subst V
                exact q22_47
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q22_48
              · have he:V = 49:=by omega
                subst V
                exact q22_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q22_50
              · have he:V = 51:=by omega
                subst V
                exact q22_51
        · by_cases h52_60:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q22_52
              · have he:V = 53:=by omega
                subst V
                exact q22_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q22_54
              · have he:V = 55:=by omega
                subst V
                exact q22_55
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q22_56
              · have he:V = 57:=by omega
                subst V
                exact q22_57
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q22_58
              · have he:V = 59:=by omega
                subst V
                exact q22_59
  · by_cases h60_121:V < 90
    · by_cases h60_90:V < 75
      · by_cases h60_75:V < 67
        · by_cases h60_67:V < 63
          · by_cases h60_63:V < 61
            · have he:V = 60:=by omega
              subst V
              exact q22_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q22_61
              · have he:V = 62:=by omega
                subst V
                exact q22_62
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q22_63
              · have he:V = 64:=by omega
                subst V
                exact q22_64
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q22_65
              · have he:V = 66:=by omega
                subst V
                exact q22_66
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q22_67
              · have he:V = 68:=by omega
                subst V
                exact q22_68
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q22_69
              · have he:V = 70:=by omega
                subst V
                exact q22_70
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q22_71
              · have he:V = 72:=by omega
                subst V
                exact q22_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q22_73
              · have he:V = 74:=by omega
                subst V
                exact q22_74
      · by_cases h75_90:V < 82
        · by_cases h75_82:V < 78
          · by_cases h75_78:V < 76
            · have he:V = 75:=by omega
              subst V
              exact q22_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q22_76
              · have he:V = 77:=by omega
                subst V
                exact q22_77
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q22_78
              · have he:V = 79:=by omega
                subst V
                exact q22_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q22_80
              · have he:V = 81:=by omega
                subst V
                exact q22_81
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q22_82
              · have he:V = 83:=by omega
                subst V
                exact q22_83
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q22_84
              · have he:V = 85:=by omega
                subst V
                exact q22_85
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q22_86
              · have he:V = 87:=by omega
                subst V
                exact q22_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q22_88
              · have he:V = 89:=by omega
                subst V
                exact q22_89
    · by_cases h90_121:V < 105
      · by_cases h90_105:V < 97
        · by_cases h90_97:V < 93
          · by_cases h90_93:V < 91
            · have he:V = 90:=by omega
              subst V
              exact q22_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q22_91
              · have he:V = 92:=by omega
                subst V
                exact q22_92
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q22_93
              · have he:V = 94:=by omega
                subst V
                exact q22_94
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q22_95
              · have he:V = 96:=by omega
                subst V
                exact q22_96
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q22_97
              · have he:V = 98:=by omega
                subst V
                exact q22_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q22_99
              · have he:V = 100:=by omega
                subst V
                exact q22_100
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q22_101
              · have he:V = 102:=by omega
                subst V
                exact q22_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q22_103
              · have he:V = 104:=by omega
                subst V
                exact q22_104
      · by_cases h105_121:V < 113
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q22_105
              · have he:V = 106:=by omega
                subst V
                exact q22_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q22_107
              · have he:V = 108:=by omega
                subst V
                exact q22_108
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q22_109
              · have he:V = 110:=by omega
                subst V
                exact q22_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q22_111
              · have he:V = 112:=by omega
                subst V
                exact q22_112
        · by_cases h113_121:V < 117
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q22_113
              · have he:V = 114:=by omega
                subst V
                exact q22_114
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q22_115
              · have he:V = 116:=by omega
                subst V
                exact q22_116
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q22_117
              · have he:V = 118:=by omega
                subst V
                exact q22_118
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q22_119
              · have he:V = 120:=by omega
                subst V
                exact q22_120
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
