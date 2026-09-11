import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked25

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q26_0:ThresholdAt 26 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 0 0 (by decide +kernel)
  | exact S 26 0 1 (by decide +kernel)
  | exact S 26 0 2 (by decide +kernel)
  | exact S 26 0 3 (by decide +kernel)
  | exact S 26 0 4 (by decide +kernel)
  | exact S 26 0 5 (by decide +kernel)
theorem q26_1:ThresholdAt 26 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 1 0 (by decide +kernel)
  | exact S 26 1 1 (by decide +kernel)
  | exact S 26 1 2 (by decide +kernel)
  | exact S 26 1 3 (by decide +kernel)
  | exact S 26 1 4 (by decide +kernel)
  | exact S 26 1 5 (by decide +kernel)
theorem q26_2:ThresholdAt 26 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 2 0 (by decide +kernel)
  | exact S 26 2 1 (by decide +kernel)
  | exact S 26 2 2 (by decide +kernel)
  | exact S 26 2 3 (by decide +kernel)
  | exact S 26 2 4 (by decide +kernel)
  | exact S 26 2 5 (by decide +kernel)
theorem q26_3:ThresholdAt 26 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 3 0 (by decide +kernel)
  | exact S 26 3 1 (by decide +kernel)
  | exact S 26 3 2 (by decide +kernel)
  | exact S 26 3 3 (by decide +kernel)
  | exact S 26 3 4 (by decide +kernel)
  | exact S 26 3 5 (by decide +kernel)
theorem q26_4:ThresholdAt 26 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 4 0 (by decide +kernel)
  | exact S 26 4 1 (by decide +kernel)
  | exact S 26 4 2 (by decide +kernel)
  | exact S 26 4 3 (by decide +kernel)
  | exact S 26 4 4 (by decide +kernel)
  | exact S 26 4 5 (by decide +kernel)
theorem q26_5:ThresholdAt 26 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 5 0 (by decide +kernel)
  | exact S 26 5 1 (by decide +kernel)
  | exact S 26 5 2 (by decide +kernel)
  | exact S 26 5 3 (by decide +kernel)
  | exact S 26 5 4 (by decide +kernel)
  | exact S 26 5 5 (by decide +kernel)
theorem q26_6:ThresholdAt 26 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 6 0 (by decide +kernel)
  | exact S 26 6 1 (by decide +kernel)
  | exact S 26 6 2 (by decide +kernel)
  | exact S 26 6 3 (by decide +kernel)
  | exact S 26 6 4 (by decide +kernel)
  | exact S 26 6 5 (by decide +kernel)
theorem q26_7:ThresholdAt 26 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 7 0 (by decide +kernel)
  | exact S 26 7 1 (by decide +kernel)
  | exact S 26 7 2 (by decide +kernel)
  | exact S 26 7 3 (by decide +kernel)
  | exact S 26 7 4 (by decide +kernel)
  | exact S 26 7 5 (by decide +kernel)
theorem q26_8:ThresholdAt 26 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 8 0 (by decide +kernel)
  | exact S 26 8 1 (by decide +kernel)
  | exact S 26 8 2 (by decide +kernel)
  | exact S 26 8 3 (by decide +kernel)
  | exact S 26 8 4 (by decide +kernel)
  | exact S 26 8 5 (by decide +kernel)
theorem q26_9:ThresholdAt 26 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 9 0 (by decide +kernel)
  | exact S 26 9 1 (by decide +kernel)
  | exact S 26 9 2 (by decide +kernel)
  | exact S 26 9 3 (by decide +kernel)
  | exact S 26 9 4 (by decide +kernel)
  | exact S 26 9 5 (by decide +kernel)
theorem q26_10:ThresholdAt 26 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 10 0 (by decide +kernel)
  | exact S 26 10 1 (by decide +kernel)
  | exact S 26 10 2 (by decide +kernel)
  | exact S 26 10 3 (by decide +kernel)
  | exact S 26 10 4 (by decide +kernel)
  | exact S 26 10 5 (by decide +kernel)
theorem q26_11:ThresholdAt 26 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 11 0 (by decide +kernel)
  | exact S 26 11 1 (by decide +kernel)
  | exact S 26 11 2 (by decide +kernel)
  | exact S 26 11 3 (by decide +kernel)
  | exact S 26 11 4 (by decide +kernel)
  | exact S 26 11 5 (by decide +kernel)
theorem q26_12:ThresholdAt 26 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 12 0 (by decide +kernel)
  | exact S 26 12 1 (by decide +kernel)
  | exact S 26 12 2 (by decide +kernel)
  | exact S 26 12 3 (by decide +kernel)
  | exact S 26 12 4 (by decide +kernel)
  | exact S 26 12 5 (by decide +kernel)
theorem q26_13:ThresholdAt 26 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 13 0 (by decide +kernel)
  | exact S 26 13 1 (by decide +kernel)
  | exact S 26 13 2 (by decide +kernel)
  | exact S 26 13 3 (by decide +kernel)
  | exact S 26 13 4 (by decide +kernel)
  | exact S 26 13 5 (by decide +kernel)
theorem q26_14:ThresholdAt 26 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 14 0 (by decide +kernel)
  | exact S 26 14 1 (by decide +kernel)
  | exact S 26 14 2 (by decide +kernel)
  | exact S 26 14 3 (by decide +kernel)
  | exact S 26 14 4 (by decide +kernel)
  | exact S 26 14 5 (by decide +kernel)
theorem q26_15:ThresholdAt 26 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 15 0 (by decide +kernel)
  | exact S 26 15 1 (by decide +kernel)
  | exact S 26 15 2 (by decide +kernel)
  | exact S 26 15 3 (by decide +kernel)
  | exact S 26 15 4 (by decide +kernel)
  | exact S 26 15 5 (by decide +kernel)
theorem q26_16:ThresholdAt 26 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 16 0 (by decide +kernel)
  | exact S 26 16 1 (by decide +kernel)
  | exact S 26 16 2 (by decide +kernel)
  | exact S 26 16 3 (by decide +kernel)
  | exact S 26 16 4 (by decide +kernel)
  | exact S 26 16 5 (by decide +kernel)
theorem q26_17:ThresholdAt 26 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 17 0 (by decide +kernel)
  | exact S 26 17 1 (by decide +kernel)
  | exact S 26 17 2 (by decide +kernel)
  | exact S 26 17 3 (by decide +kernel)
  | exact S 26 17 4 (by decide +kernel)
  | exact S 26 17 5 (by decide +kernel)
theorem q26_18:ThresholdAt 26 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 18 0 (by decide +kernel)
  | exact S 26 18 1 (by decide +kernel)
  | exact S 26 18 2 (by decide +kernel)
  | exact S 26 18 3 (by decide +kernel)
  | exact S 26 18 4 (by decide +kernel)
  | exact S 26 18 5 (by decide +kernel)
theorem q26_19:ThresholdAt 26 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 19 0 (by decide +kernel)
  | exact S 26 19 1 (by decide +kernel)
  | exact S 26 19 2 (by decide +kernel)
  | exact S 26 19 3 (by decide +kernel)
  | exact S 26 19 4 (by decide +kernel)
  | exact S 26 19 5 (by decide +kernel)
theorem q26_20:ThresholdAt 26 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 20 0 (by decide +kernel)
  | exact S 26 20 1 (by decide +kernel)
  | exact S 26 20 2 (by decide +kernel)
  | exact S 26 20 3 (by decide +kernel)
  | exact S 26 20 4 (by decide +kernel)
  | exact S 26 20 5 (by decide +kernel)
theorem q26_21:ThresholdAt 26 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 21 0 (by decide +kernel)
  | exact S 26 21 1 (by decide +kernel)
  | exact S 26 21 2 (by decide +kernel)
  | exact S 26 21 3 (by decide +kernel)
  | exact S 26 21 4 (by decide +kernel)
  | exact S 26 21 5 (by decide +kernel)
theorem q26_22:ThresholdAt 26 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 22 0 (by decide +kernel)
  | exact S 26 22 1 (by decide +kernel)
  | exact S 26 22 2 (by decide +kernel)
  | exact S 26 22 3 (by decide +kernel)
  | exact S 26 22 4 (by decide +kernel)
  | exact S 26 22 5 (by decide +kernel)
theorem q26_23:ThresholdAt 26 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 23 0 (by decide +kernel)
  | exact S 26 23 1 (by decide +kernel)
  | exact S 26 23 2 (by decide +kernel)
  | exact S 26 23 3 (by decide +kernel)
  | exact S 26 23 4 (by decide +kernel)
  | exact S 26 23 5 (by decide +kernel)
theorem q26_24:ThresholdAt 26 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 24 0 (by decide +kernel)
  | exact S 26 24 1 (by decide +kernel)
  | exact S 26 24 2 (by decide +kernel)
  | exact S 26 24 3 (by decide +kernel)
  | exact S 26 24 4 (by decide +kernel)
  | exact S 26 24 5 (by decide +kernel)
theorem q26_25:ThresholdAt 26 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 25 0 (by decide +kernel)
  | exact S 26 25 1 (by decide +kernel)
  | exact S 26 25 2 (by decide +kernel)
  | exact S 26 25 3 (by decide +kernel)
  | exact S 26 25 4 (by decide +kernel)
  | exact S 26 25 5 (by decide +kernel)
theorem q26_26:ThresholdAt 26 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 26 0 (by decide +kernel)
  | exact S 26 26 1 (by decide +kernel)
  | exact S 26 26 2 (by decide +kernel)
  | exact S 26 26 3 (by decide +kernel)
  | exact S 26 26 4 (by decide +kernel)
  | exact S 26 26 5 (by decide +kernel)
theorem q26_27:ThresholdAt 26 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 27 0 (by decide +kernel)
  | exact S 26 27 1 (by decide +kernel)
  | exact S 26 27 2 (by decide +kernel)
  | exact S 26 27 3 (by decide +kernel)
  | exact S 26 27 4 (by decide +kernel)
  | exact S 26 27 5 (by decide +kernel)
theorem q26_28:ThresholdAt 26 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 28 0 (by decide +kernel)
  | exact S 26 28 1 (by decide +kernel)
  | exact S 26 28 2 (by decide +kernel)
  | exact S 26 28 3 (by decide +kernel)
  | exact S 26 28 4 (by decide +kernel)
  | exact S 26 28 5 (by decide +kernel)
theorem q26_29:ThresholdAt 26 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 29 0 (by decide +kernel)
  | exact S 26 29 1 (by decide +kernel)
  | exact S 26 29 2 (by decide +kernel)
  | exact S 26 29 3 (by decide +kernel)
  | exact S 26 29 4 (by decide +kernel)
  | exact S 26 29 5 (by decide +kernel)
theorem q26_30:ThresholdAt 26 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 30 0 (by decide +kernel)
  | exact S 26 30 1 (by decide +kernel)
  | exact S 26 30 2 (by decide +kernel)
  | exact S 26 30 3 (by decide +kernel)
  | exact S 26 30 4 (by decide +kernel)
  | exact S 26 30 5 (by decide +kernel)
theorem q26_31:ThresholdAt 26 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 31 0 (by decide +kernel)
  | exact S 26 31 1 (by decide +kernel)
  | exact S 26 31 2 (by decide +kernel)
  | exact S 26 31 3 (by decide +kernel)
  | exact S 26 31 4 (by decide +kernel)
  | exact S 26 31 5 (by decide +kernel)
theorem q26_32:ThresholdAt 26 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 32 0 (by decide +kernel)
  | exact S 26 32 1 (by decide +kernel)
  | exact S 26 32 2 (by decide +kernel)
  | exact S 26 32 3 (by decide +kernel)
  | exact S 26 32 4 (by decide +kernel)
  | exact S 26 32 5 (by decide +kernel)
theorem q26_33:ThresholdAt 26 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 33 0 (by decide +kernel)
  | exact S 26 33 1 (by decide +kernel)
  | exact S 26 33 2 (by decide +kernel)
  | exact S 26 33 3 (by decide +kernel)
  | exact S 26 33 4 (by decide +kernel)
  | exact S 26 33 5 (by decide +kernel)
theorem q26_34:ThresholdAt 26 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 34 0 (by decide +kernel)
  | exact S 26 34 1 (by decide +kernel)
  | exact S 26 34 2 (by decide +kernel)
  | exact S 26 34 3 (by decide +kernel)
  | exact S 26 34 4 (by decide +kernel)
  | exact S 26 34 5 (by decide +kernel)
theorem q26_35:ThresholdAt 26 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 35 0 (by decide +kernel)
  | exact S 26 35 1 (by decide +kernel)
  | exact S 26 35 2 (by decide +kernel)
  | exact S 26 35 3 (by decide +kernel)
  | exact S 26 35 4 (by decide +kernel)
  | exact S 26 35 5 (by decide +kernel)
theorem q26_36:ThresholdAt 26 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 36 0 (by decide +kernel)
  | exact S 26 36 1 (by decide +kernel)
  | exact S 26 36 2 (by decide +kernel)
  | exact S 26 36 3 (by decide +kernel)
  | exact S 26 36 4 (by decide +kernel)
  | exact S 26 36 5 (by decide +kernel)
theorem q26_37:ThresholdAt 26 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 37 0 (by decide +kernel)
  | exact S 26 37 1 (by decide +kernel)
  | exact S 26 37 2 (by decide +kernel)
  | exact S 26 37 3 (by decide +kernel)
  | exact S 26 37 4 (by decide +kernel)
  | exact S 26 37 5 (by decide +kernel)
theorem q26_38:ThresholdAt 26 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 38 0 (by decide +kernel)
  | exact S 26 38 1 (by decide +kernel)
  | exact S 26 38 2 (by decide +kernel)
  | exact S 26 38 3 (by decide +kernel)
  | exact S 26 38 4 (by decide +kernel)
  | exact S 26 38 5 (by decide +kernel)
theorem q26_39:ThresholdAt 26 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 39 0 (by decide +kernel)
  | exact S 26 39 1 (by decide +kernel)
  | exact S 26 39 2 (by decide +kernel)
  | exact S 26 39 3 (by decide +kernel)
  | exact S 26 39 4 (by decide +kernel)
  | exact S 26 39 5 (by decide +kernel)
theorem q26_40:ThresholdAt 26 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 40 0 (by decide +kernel)
  | exact S 26 40 1 (by decide +kernel)
  | exact S 26 40 2 (by decide +kernel)
  | exact S 26 40 3 (by decide +kernel)
  | exact S 26 40 4 (by decide +kernel)
  | exact S 26 40 5 (by decide +kernel)
theorem q26_41:ThresholdAt 26 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 41 0 (by decide +kernel)
  | exact S 26 41 1 (by decide +kernel)
  | exact S 26 41 2 (by decide +kernel)
  | exact S 26 41 3 (by decide +kernel)
  | exact S 26 41 4 (by decide +kernel)
  | exact S 26 41 5 (by decide +kernel)
theorem q26_42:ThresholdAt 26 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 42 0 (by decide +kernel)
  | exact S 26 42 1 (by decide +kernel)
  | exact S 26 42 2 (by decide +kernel)
  | exact S 26 42 3 (by decide +kernel)
  | exact S 26 42 4 (by decide +kernel)
  | exact S 26 42 5 (by decide +kernel)
theorem q26_43:ThresholdAt 26 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 43 0 (by decide +kernel)
  | exact S 26 43 1 (by decide +kernel)
  | exact S 26 43 2 (by decide +kernel)
  | exact S 26 43 3 (by decide +kernel)
  | exact S 26 43 4 (by decide +kernel)
  | exact S 26 43 5 (by decide +kernel)
theorem q26_44:ThresholdAt 26 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 44 0 (by decide +kernel)
  | exact S 26 44 1 (by decide +kernel)
  | exact S 26 44 2 (by decide +kernel)
  | exact S 26 44 3 (by decide +kernel)
  | exact S 26 44 4 (by decide +kernel)
  | exact S 26 44 5 (by decide +kernel)
theorem q26_45:ThresholdAt 26 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 45 0 (by decide +kernel)
  | exact S 26 45 1 (by decide +kernel)
  | exact S 26 45 2 (by decide +kernel)
  | exact S 26 45 3 (by decide +kernel)
  | exact S 26 45 4 (by decide +kernel)
  | exact S 26 45 5 (by decide +kernel)
theorem q26_46:ThresholdAt 26 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 46 0 (by decide +kernel)
  | exact S 26 46 1 (by decide +kernel)
  | exact S 26 46 2 (by decide +kernel)
  | exact S 26 46 3 (by decide +kernel)
  | exact S 26 46 4 (by decide +kernel)
  | exact S 26 46 5 (by decide +kernel)
theorem q26_47:ThresholdAt 26 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 47 0 (by decide +kernel)
  | exact S 26 47 1 (by decide +kernel)
  | exact S 26 47 2 (by decide +kernel)
  | exact S 26 47 3 (by decide +kernel)
  | exact S 26 47 4 (by decide +kernel)
  | exact S 26 47 5 (by decide +kernel)
theorem q26_48:ThresholdAt 26 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 48 0 (by decide +kernel)
  | exact S 26 48 1 (by decide +kernel)
  | exact S 26 48 2 (by decide +kernel)
  | exact S 26 48 3 (by decide +kernel)
  | exact S 26 48 4 (by decide +kernel)
  | exact S 26 48 5 (by decide +kernel)
theorem q26_49:ThresholdAt 26 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 49 0 (by decide +kernel)
  | exact S 26 49 1 (by decide +kernel)
  | exact S 26 49 2 (by decide +kernel)
  | exact S 26 49 3 (by decide +kernel)
  | exact S 26 49 4 (by decide +kernel)
  | exact S 26 49 5 (by decide +kernel)
theorem q26_50:ThresholdAt 26 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 50 0 (by decide +kernel)
  | exact S 26 50 1 (by decide +kernel)
  | exact S 26 50 2 (by decide +kernel)
  | exact S 26 50 3 (by decide +kernel)
  | exact S 26 50 4 (by decide +kernel)
  | exact S 26 50 5 (by decide +kernel)
theorem q26_51:ThresholdAt 26 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 51 0 (by decide +kernel)
  | exact S 26 51 1 (by decide +kernel)
  | exact S 26 51 2 (by decide +kernel)
  | exact S 26 51 3 (by decide +kernel)
  | exact S 26 51 4 (by decide +kernel)
  | exact S 26 51 5 (by decide +kernel)
theorem q26_52:ThresholdAt 26 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 52 0 (by decide +kernel)
  | exact S 26 52 1 (by decide +kernel)
  | exact S 26 52 2 (by decide +kernel)
  | exact S 26 52 3 (by decide +kernel)
  | exact S 26 52 4 (by decide +kernel)
  | exact S 26 52 5 (by decide +kernel)
theorem q26_53:ThresholdAt 26 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 53 0 (by decide +kernel)
  | exact S 26 53 1 (by decide +kernel)
  | exact S 26 53 2 (by decide +kernel)
  | exact S 26 53 3 (by decide +kernel)
  | exact S 26 53 4 (by decide +kernel)
  | exact S 26 53 5 (by decide +kernel)
theorem q26_54:ThresholdAt 26 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 54 0 (by decide +kernel)
  | exact S 26 54 1 (by decide +kernel)
  | exact S 26 54 2 (by decide +kernel)
  | exact S 26 54 3 (by decide +kernel)
  | exact S 26 54 4 (by decide +kernel)
  | exact S 26 54 5 (by decide +kernel)
theorem q26_55:ThresholdAt 26 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 55 0 (by decide +kernel)
  | exact S 26 55 1 (by decide +kernel)
  | exact S 26 55 2 (by decide +kernel)
  | exact S 26 55 3 (by decide +kernel)
  | exact S 26 55 4 (by decide +kernel)
  | exact S 26 55 5 (by decide +kernel)
theorem q26_56:ThresholdAt 26 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 56 0 (by decide +kernel)
  | exact S 26 56 1 (by decide +kernel)
  | exact S 26 56 2 (by decide +kernel)
  | exact S 26 56 3 (by decide +kernel)
  | exact S 26 56 4 (by decide +kernel)
  | exact S 26 56 5 (by decide +kernel)
theorem q26_57:ThresholdAt 26 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 57 0 (by decide +kernel)
  | exact S 26 57 1 (by decide +kernel)
  | exact S 26 57 2 (by decide +kernel)
  | exact S 26 57 3 (by decide +kernel)
  | exact S 26 57 4 (by decide +kernel)
  | exact S 26 57 5 (by decide +kernel)
theorem q26_58:ThresholdAt 26 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 58 0 (by decide +kernel)
  | exact S 26 58 1 (by decide +kernel)
  | exact S 26 58 2 (by decide +kernel)
  | exact S 26 58 3 (by decide +kernel)
  | exact S 26 58 4 (by decide +kernel)
  | exact S 26 58 5 (by decide +kernel)
theorem q26_59:ThresholdAt 26 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 59 0 (by decide +kernel)
  | exact S 26 59 1 (by decide +kernel)
  | exact S 26 59 2 (by decide +kernel)
  | exact S 26 59 3 (by decide +kernel)
  | exact S 26 59 4 (by decide +kernel)
  | exact S 26 59 5 (by decide +kernel)
theorem q26_60:ThresholdAt 26 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 60 0 (by decide +kernel)
  | exact S 26 60 1 (by decide +kernel)
  | exact S 26 60 2 (by decide +kernel)
  | exact S 26 60 3 (by decide +kernel)
  | exact S 26 60 4 (by decide +kernel)
  | exact S 26 60 5 (by decide +kernel)
theorem q26_61:ThresholdAt 26 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 61 0 (by decide +kernel)
  | exact S 26 61 1 (by decide +kernel)
  | exact S 26 61 2 (by decide +kernel)
  | exact S 26 61 3 (by decide +kernel)
  | exact S 26 61 4 (by decide +kernel)
  | exact S 26 61 5 (by decide +kernel)
theorem q26_62:ThresholdAt 26 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 62 0 (by decide +kernel)
  | exact S 26 62 1 (by decide +kernel)
  | exact S 26 62 2 (by decide +kernel)
  | exact S 26 62 3 (by decide +kernel)
  | exact S 26 62 4 (by decide +kernel)
  | exact S 26 62 5 (by decide +kernel)
theorem q26_63:ThresholdAt 26 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 63 0 (by decide +kernel)
  | exact S 26 63 1 (by decide +kernel)
  | exact S 26 63 2 (by decide +kernel)
  | exact S 26 63 3 (by decide +kernel)
  | exact S 26 63 4 (by decide +kernel)
  | exact S 26 63 5 (by decide +kernel)
theorem q26_64:ThresholdAt 26 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 64 0 (by decide +kernel)
  | exact S 26 64 1 (by decide +kernel)
  | exact S 26 64 2 (by decide +kernel)
  | exact S 26 64 3 (by decide +kernel)
  | exact S 26 64 4 (by decide +kernel)
  | exact S 26 64 5 (by decide +kernel)
theorem q26_65:ThresholdAt 26 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 65 0 (by decide +kernel)
  | exact S 26 65 1 (by decide +kernel)
  | exact S 26 65 2 (by decide +kernel)
  | exact S 26 65 3 (by decide +kernel)
  | exact S 26 65 4 (by decide +kernel)
  | exact S 26 65 5 (by decide +kernel)
theorem q26_66:ThresholdAt 26 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 66 0 (by decide +kernel)
  | exact S 26 66 1 (by decide +kernel)
  | exact S 26 66 2 (by decide +kernel)
  | exact S 26 66 3 (by decide +kernel)
  | exact S 26 66 4 (by decide +kernel)
  | exact S 26 66 5 (by decide +kernel)
theorem q26_67:ThresholdAt 26 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 67 0 (by decide +kernel)
  | exact S 26 67 1 (by decide +kernel)
  | exact S 26 67 2 (by decide +kernel)
  | exact S 26 67 3 (by decide +kernel)
  | exact S 26 67 4 (by decide +kernel)
  | exact S 26 67 5 (by decide +kernel)
theorem q26_68:ThresholdAt 26 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 68 0 (by decide +kernel)
  | exact S 26 68 1 (by decide +kernel)
  | exact S 26 68 2 (by decide +kernel)
  | exact S 26 68 3 (by decide +kernel)
  | exact S 26 68 4 (by decide +kernel)
  | exact S 26 68 5 (by decide +kernel)
theorem q26_69:ThresholdAt 26 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 69 0 (by decide +kernel)
  | exact S 26 69 1 (by decide +kernel)
  | exact S 26 69 2 (by decide +kernel)
  | exact S 26 69 3 (by decide +kernel)
  | exact S 26 69 4 (by decide +kernel)
  | exact S 26 69 5 (by decide +kernel)
theorem q26_70:ThresholdAt 26 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 70 0 (by decide +kernel)
  | exact S 26 70 1 (by decide +kernel)
  | exact S 26 70 2 (by decide +kernel)
  | exact S 26 70 3 (by decide +kernel)
  | exact S 26 70 4 (by decide +kernel)
  | exact S 26 70 5 (by decide +kernel)
theorem q26_71:ThresholdAt 26 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 71 0 (by decide +kernel)
  | exact S 26 71 1 (by decide +kernel)
  | exact S 26 71 2 (by decide +kernel)
  | exact S 26 71 3 (by decide +kernel)
  | exact S 26 71 4 (by decide +kernel)
  | exact S 26 71 5 (by decide +kernel)
theorem q26_72:ThresholdAt 26 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 72 0 (by decide +kernel)
  | exact S 26 72 1 (by decide +kernel)
  | exact S 26 72 2 (by decide +kernel)
  | exact S 26 72 3 (by decide +kernel)
  | exact S 26 72 4 (by decide +kernel)
  | exact S 26 72 5 (by decide +kernel)
theorem q26_73:ThresholdAt 26 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 73 0 (by decide +kernel)
  | exact S 26 73 1 (by decide +kernel)
  | exact S 26 73 2 (by decide +kernel)
  | exact S 26 73 3 (by decide +kernel)
  | exact S 26 73 4 (by decide +kernel)
  | exact S 26 73 5 (by decide +kernel)
theorem q26_74:ThresholdAt 26 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 74 0 (by decide +kernel)
  | exact S 26 74 1 (by decide +kernel)
  | exact S 26 74 2 (by decide +kernel)
  | exact S 26 74 3 (by decide +kernel)
  | exact S 26 74 4 (by decide +kernel)
  | exact S 26 74 5 (by decide +kernel)
theorem q26_75:ThresholdAt 26 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 75 0 (by decide +kernel)
  | exact S 26 75 1 (by decide +kernel)
  | exact S 26 75 2 (by decide +kernel)
  | exact S 26 75 3 (by decide +kernel)
  | exact S 26 75 4 (by decide +kernel)
  | exact S 26 75 5 (by decide +kernel)
theorem q26_76:ThresholdAt 26 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 76 0 (by decide +kernel)
  | exact S 26 76 1 (by decide +kernel)
  | exact S 26 76 2 (by decide +kernel)
  | exact S 26 76 3 (by decide +kernel)
  | exact S 26 76 4 (by decide +kernel)
  | exact S 26 76 5 (by decide +kernel)
theorem q26_77:ThresholdAt 26 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 77 0 (by decide +kernel)
  | exact S 26 77 1 (by decide +kernel)
  | exact S 26 77 2 (by decide +kernel)
  | exact S 26 77 3 (by decide +kernel)
  | exact S 26 77 4 (by decide +kernel)
  | exact S 26 77 5 (by decide +kernel)
theorem q26_78:ThresholdAt 26 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 78 0 (by decide +kernel)
  | exact S 26 78 1 (by decide +kernel)
  | exact S 26 78 2 (by decide +kernel)
  | exact S 26 78 3 (by decide +kernel)
  | exact S 26 78 4 (by decide +kernel)
  | exact S 26 78 5 (by decide +kernel)
theorem q26_79:ThresholdAt 26 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 79 0 (by decide +kernel)
  | exact S 26 79 1 (by decide +kernel)
  | exact S 26 79 2 (by decide +kernel)
  | exact S 26 79 3 (by decide +kernel)
  | exact S 26 79 4 (by decide +kernel)
  | exact S 26 79 5 (by decide +kernel)
theorem q26_80:ThresholdAt 26 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 80 0 (by decide +kernel)
  | exact S 26 80 1 (by decide +kernel)
  | exact S 26 80 2 (by decide +kernel)
  | exact S 26 80 3 (by decide +kernel)
  | exact S 26 80 4 (by decide +kernel)
  | exact S 26 80 5 (by decide +kernel)
theorem q26_81:ThresholdAt 26 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 81 0 (by decide +kernel)
  | exact S 26 81 1 (by decide +kernel)
  | exact S 26 81 2 (by decide +kernel)
  | exact S 26 81 3 (by decide +kernel)
  | exact S 26 81 4 (by decide +kernel)
  | exact S 26 81 5 (by decide +kernel)
theorem q26_82:ThresholdAt 26 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 82 0 (by decide +kernel)
  | exact S 26 82 1 (by decide +kernel)
  | exact S 26 82 2 (by decide +kernel)
  | exact S 26 82 3 (by decide +kernel)
  | exact S 26 82 4 (by decide +kernel)
  | exact S 26 82 5 (by decide +kernel)
theorem q26_83:ThresholdAt 26 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 83 0 (by decide +kernel)
  | exact S 26 83 1 (by decide +kernel)
  | exact S 26 83 2 (by decide +kernel)
  | exact S 26 83 3 (by decide +kernel)
  | exact S 26 83 4 (by decide +kernel)
  | exact S 26 83 5 (by decide +kernel)
theorem q26_84:ThresholdAt 26 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 84 0 (by decide +kernel)
  | exact S 26 84 1 (by decide +kernel)
  | exact S 26 84 2 (by decide +kernel)
  | exact S 26 84 3 (by decide +kernel)
  | exact S 26 84 4 (by decide +kernel)
  | exact S 26 84 5 (by decide +kernel)
theorem q26_85:ThresholdAt 26 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 85 0 (by decide +kernel)
  | exact S 26 85 1 (by decide +kernel)
  | exact S 26 85 2 (by decide +kernel)
  | exact S 26 85 3 (by decide +kernel)
  | exact S 26 85 4 (by decide +kernel)
  | exact S 26 85 5 (by decide +kernel)
theorem q26_86:ThresholdAt 26 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 86 0 (by decide +kernel)
  | exact S 26 86 1 (by decide +kernel)
  | exact S 26 86 2 (by decide +kernel)
  | exact S 26 86 3 (by decide +kernel)
  | exact S 26 86 4 (by decide +kernel)
  | exact S 26 86 5 (by decide +kernel)
theorem q26_87:ThresholdAt 26 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 87 0 (by decide +kernel)
  | exact S 26 87 1 (by decide +kernel)
  | exact S 26 87 2 (by decide +kernel)
  | exact S 26 87 3 (by decide +kernel)
  | exact S 26 87 4 (by decide +kernel)
  | exact S 26 87 5 (by decide +kernel)
theorem q26_88:ThresholdAt 26 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 88 0 (by decide +kernel)
  | exact S 26 88 1 (by decide +kernel)
  | exact S 26 88 2 (by decide +kernel)
  | exact S 26 88 3 (by decide +kernel)
  | exact S 26 88 4 (by decide +kernel)
  | exact S 26 88 5 (by decide +kernel)
theorem q26_89:ThresholdAt 26 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 89 0 (by decide +kernel)
  | exact S 26 89 1 (by decide +kernel)
  | exact S 26 89 2 (by decide +kernel)
  | exact S 26 89 3 (by decide +kernel)
  | exact S 26 89 4 (by decide +kernel)
  | exact S 26 89 5 (by decide +kernel)
theorem q26_90:ThresholdAt 26 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 90 0 (by decide +kernel)
  | exact S 26 90 1 (by decide +kernel)
  | exact S 26 90 2 (by decide +kernel)
  | exact S 26 90 3 (by decide +kernel)
  | exact S 26 90 4 (by decide +kernel)
  | exact S 26 90 5 (by decide +kernel)
theorem q26_91:ThresholdAt 26 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 91 0 (by decide +kernel)
  | exact S 26 91 1 (by decide +kernel)
  | exact S 26 91 2 (by decide +kernel)
  | exact S 26 91 3 (by decide +kernel)
  | exact S 26 91 4 (by decide +kernel)
  | exact S 26 91 5 (by decide +kernel)
theorem q26_92:ThresholdAt 26 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 92 0 (by decide +kernel)
  | exact S 26 92 1 (by decide +kernel)
  | exact S 26 92 2 (by decide +kernel)
  | exact S 26 92 3 (by decide +kernel)
  | exact S 26 92 4 (by decide +kernel)
  | exact S 26 92 5 (by decide +kernel)
theorem q26_93:ThresholdAt 26 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 93 0 (by decide +kernel)
  | exact S 26 93 1 (by decide +kernel)
  | exact S 26 93 2 (by decide +kernel)
  | exact S 26 93 3 (by decide +kernel)
  | exact S 26 93 4 (by decide +kernel)
  | exact S 26 93 5 (by decide +kernel)
theorem q26_94:ThresholdAt 26 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 94 0 (by decide +kernel)
  | exact S 26 94 1 (by decide +kernel)
  | exact S 26 94 2 (by decide +kernel)
  | exact S 26 94 3 (by decide +kernel)
  | exact S 26 94 4 (by decide +kernel)
  | exact S 26 94 5 (by decide +kernel)
theorem q26_95:ThresholdAt 26 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 95 0 (by decide +kernel)
  | exact S 26 95 1 (by decide +kernel)
  | exact S 26 95 2 (by decide +kernel)
  | exact S 26 95 3 (by decide +kernel)
  | exact S 26 95 4 (by decide +kernel)
  | exact S 26 95 5 (by decide +kernel)
theorem q26_96:ThresholdAt 26 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 96 0 (by decide +kernel)
  | exact S 26 96 1 (by decide +kernel)
  | exact S 26 96 2 (by decide +kernel)
  | exact S 26 96 3 (by decide +kernel)
  | exact S 26 96 4 (by decide +kernel)
  | exact S 26 96 5 (by decide +kernel)
theorem q26_97:ThresholdAt 26 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 97 0 (by decide +kernel)
  | exact S 26 97 1 (by decide +kernel)
  | exact S 26 97 2 (by decide +kernel)
  | exact S 26 97 3 (by decide +kernel)
  | exact S 26 97 4 (by decide +kernel)
  | exact S 26 97 5 (by decide +kernel)
theorem q26_98:ThresholdAt 26 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 98 0 (by decide +kernel)
  | exact S 26 98 1 (by decide +kernel)
  | exact S 26 98 2 (by decide +kernel)
  | exact S 26 98 3 (by decide +kernel)
  | exact S 26 98 4 (by decide +kernel)
  | exact S 26 98 5 (by decide +kernel)
theorem q26_99:ThresholdAt 26 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 99 0 (by decide +kernel)
  | exact S 26 99 1 (by decide +kernel)
  | exact S 26 99 2 (by decide +kernel)
  | exact S 26 99 3 (by decide +kernel)
  | exact S 26 99 4 (by decide +kernel)
  | exact S 26 99 5 (by decide +kernel)
theorem q26_100:ThresholdAt 26 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 100 0 (by decide +kernel)
  | exact S 26 100 1 (by decide +kernel)
  | exact S 26 100 2 (by decide +kernel)
  | exact S 26 100 3 (by decide +kernel)
  | exact S 26 100 4 (by decide +kernel)
  | exact S 26 100 5 (by decide +kernel)
theorem q26_101:ThresholdAt 26 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 101 0 (by decide +kernel)
  | exact S 26 101 1 (by decide +kernel)
  | exact S 26 101 2 (by decide +kernel)
  | exact S 26 101 3 (by decide +kernel)
  | exact S 26 101 4 (by decide +kernel)
  | exact S 26 101 5 (by decide +kernel)
theorem q26_102:ThresholdAt 26 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 102 0 (by decide +kernel)
  | exact S 26 102 1 (by decide +kernel)
  | exact S 26 102 2 (by decide +kernel)
  | exact S 26 102 3 (by decide +kernel)
  | exact S 26 102 4 (by decide +kernel)
  | exact S 26 102 5 (by decide +kernel)
theorem q26_103:ThresholdAt 26 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 103 0 (by decide +kernel)
  | exact S 26 103 1 (by decide +kernel)
  | exact S 26 103 2 (by decide +kernel)
  | exact S 26 103 3 (by decide +kernel)
  | exact S 26 103 4 (by decide +kernel)
  | exact S 26 103 5 (by decide +kernel)
theorem q26_104:ThresholdAt 26 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 104 0 (by decide +kernel)
  | exact S 26 104 1 (by decide +kernel)
  | exact S 26 104 2 (by decide +kernel)
  | exact S 26 104 3 (by decide +kernel)
  | exact S 26 104 4 (by decide +kernel)
  | exact S 26 104 5 (by decide +kernel)
theorem q26_105:ThresholdAt 26 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 105 0 (by decide +kernel)
  | exact S 26 105 1 (by decide +kernel)
  | exact S 26 105 2 (by decide +kernel)
  | exact S 26 105 3 (by decide +kernel)
  | exact S 26 105 4 (by decide +kernel)
  | exact S 26 105 5 (by decide +kernel)
theorem q26_106:ThresholdAt 26 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 106 0 (by decide +kernel)
  | exact S 26 106 1 (by decide +kernel)
  | exact S 26 106 2 (by decide +kernel)
  | exact S 26 106 3 (by decide +kernel)
  | exact S 26 106 4 (by decide +kernel)
  | exact S 26 106 5 (by decide +kernel)
theorem q26_107:ThresholdAt 26 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 107 0 (by decide +kernel)
  | exact S 26 107 1 (by decide +kernel)
  | exact S 26 107 2 (by decide +kernel)
  | exact S 26 107 3 (by decide +kernel)
  | exact S 26 107 4 (by decide +kernel)
  | exact S 26 107 5 (by decide +kernel)
theorem q26_108:ThresholdAt 26 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 108 0 (by decide +kernel)
  | exact S 26 108 1 (by decide +kernel)
  | exact S 26 108 2 (by decide +kernel)
  | exact S 26 108 3 (by decide +kernel)
  | exact S 26 108 4 (by decide +kernel)
  | exact S 26 108 5 (by decide +kernel)
theorem q26_109:ThresholdAt 26 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 109 0 (by decide +kernel)
  | exact S 26 109 1 (by decide +kernel)
  | exact S 26 109 2 (by decide +kernel)
  | exact S 26 109 3 (by decide +kernel)
  | exact S 26 109 4 (by decide +kernel)
  | exact S 26 109 5 (by decide +kernel)
theorem q26_110:ThresholdAt 26 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 110 0 (by decide +kernel)
  | exact S 26 110 1 (by decide +kernel)
  | exact S 26 110 2 (by decide +kernel)
  | exact S 26 110 3 (by decide +kernel)
  | exact S 26 110 4 (by decide +kernel)
  | exact S 26 110 5 (by decide +kernel)
theorem q26_111:ThresholdAt 26 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 111 0 (by decide +kernel)
  | exact S 26 111 1 (by decide +kernel)
  | exact S 26 111 2 (by decide +kernel)
  | exact S 26 111 3 (by decide +kernel)
  | exact S 26 111 4 (by decide +kernel)
  | exact S 26 111 5 (by decide +kernel)
theorem q26_112:ThresholdAt 26 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 112 0 (by decide +kernel)
  | exact S 26 112 1 (by decide +kernel)
  | exact S 26 112 2 (by decide +kernel)
  | exact S 26 112 3 (by decide +kernel)
  | exact S 26 112 4 (by decide +kernel)
  | exact S 26 112 5 (by decide +kernel)
theorem q26_113:ThresholdAt 26 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 113 0 (by decide +kernel)
  | exact S 26 113 1 (by decide +kernel)
  | exact S 26 113 2 (by decide +kernel)
  | exact S 26 113 3 (by decide +kernel)
  | exact S 26 113 4 (by decide +kernel)
  | exact S 26 113 5 (by decide +kernel)
theorem q26_114:ThresholdAt 26 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 114 0 (by decide +kernel)
  | exact S 26 114 1 (by decide +kernel)
  | exact S 26 114 2 (by decide +kernel)
  | exact S 26 114 3 (by decide +kernel)
  | exact S 26 114 4 (by decide +kernel)
  | exact S 26 114 5 (by decide +kernel)
theorem q26_115:ThresholdAt 26 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 115 0 (by decide +kernel)
  | exact S 26 115 1 (by decide +kernel)
  | exact S 26 115 2 (by decide +kernel)
  | exact S 26 115 3 (by decide +kernel)
  | exact S 26 115 4 (by decide +kernel)
  | exact S 26 115 5 (by decide +kernel)
theorem q26_116:ThresholdAt 26 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 116 0 (by decide +kernel)
  | exact S 26 116 1 (by decide +kernel)
  | exact S 26 116 2 (by decide +kernel)
  | exact S 26 116 3 (by decide +kernel)
  | exact S 26 116 4 (by decide +kernel)
  | exact S 26 116 5 (by decide +kernel)
theorem checkedR26:∀ V ∈ List.range 117,ThresholdAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0_117:V < 58
  · by_cases h0_58:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q26_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q26_1
              · have he:V = 2:=by omega
                subst V
                exact q26_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q26_3
              · have he:V = 4:=by omega
                subst V
                exact q26_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q26_5
              · have he:V = 6:=by omega
                subst V
                exact q26_6
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have he:V = 7:=by omega
              subst V
              exact q26_7
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q26_8
              · have he:V = 9:=by omega
                subst V
                exact q26_9
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q26_10
              · have he:V = 11:=by omega
                subst V
                exact q26_11
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q26_12
              · have he:V = 13:=by omega
                subst V
                exact q26_13
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have he:V = 14:=by omega
              subst V
              exact q26_14
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q26_15
              · have he:V = 16:=by omega
                subst V
                exact q26_16
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q26_17
              · have he:V = 18:=by omega
                subst V
                exact q26_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q26_19
              · have he:V = 20:=by omega
                subst V
                exact q26_20
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q26_21
              · have he:V = 22:=by omega
                subst V
                exact q26_22
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q26_23
              · have he:V = 24:=by omega
                subst V
                exact q26_24
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q26_25
              · have he:V = 26:=by omega
                subst V
                exact q26_26
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q26_27
              · have he:V = 28:=by omega
                subst V
                exact q26_28
    · by_cases h29_58:V < 43
      · by_cases h29_43:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have he:V = 29:=by omega
              subst V
              exact q26_29
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q26_30
              · have he:V = 31:=by omega
                subst V
                exact q26_31
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q26_32
              · have he:V = 33:=by omega
                subst V
                exact q26_33
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q26_34
              · have he:V = 35:=by omega
                subst V
                exact q26_35
        · by_cases h36_43:V < 39
          · by_cases h36_39:V < 37
            · have he:V = 36:=by omega
              subst V
              exact q26_36
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q26_37
              · have he:V = 38:=by omega
                subst V
                exact q26_38
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q26_39
              · have he:V = 40:=by omega
                subst V
                exact q26_40
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q26_41
              · have he:V = 42:=by omega
                subst V
                exact q26_42
      · by_cases h43_58:V < 50
        · by_cases h43_50:V < 46
          · by_cases h43_46:V < 44
            · have he:V = 43:=by omega
              subst V
              exact q26_43
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q26_44
              · have he:V = 45:=by omega
                subst V
                exact q26_45
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q26_46
              · have he:V = 47:=by omega
                subst V
                exact q26_47
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q26_48
              · have he:V = 49:=by omega
                subst V
                exact q26_49
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q26_50
              · have he:V = 51:=by omega
                subst V
                exact q26_51
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q26_52
              · have he:V = 53:=by omega
                subst V
                exact q26_53
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q26_54
              · have he:V = 55:=by omega
                subst V
                exact q26_55
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q26_56
              · have he:V = 57:=by omega
                subst V
                exact q26_57
  · by_cases h58_117:V < 87
    · by_cases h58_87:V < 72
      · by_cases h58_72:V < 65
        · by_cases h58_65:V < 61
          · by_cases h58_61:V < 59
            · have he:V = 58:=by omega
              subst V
              exact q26_58
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q26_59
              · have he:V = 60:=by omega
                subst V
                exact q26_60
          · by_cases h61_65:V < 63
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q26_61
              · have he:V = 62:=by omega
                subst V
                exact q26_62
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q26_63
              · have he:V = 64:=by omega
                subst V
                exact q26_64
        · by_cases h65_72:V < 68
          · by_cases h65_68:V < 66
            · have he:V = 65:=by omega
              subst V
              exact q26_65
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q26_66
              · have he:V = 67:=by omega
                subst V
                exact q26_67
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q26_68
              · have he:V = 69:=by omega
                subst V
                exact q26_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q26_70
              · have he:V = 71:=by omega
                subst V
                exact q26_71
      · by_cases h72_87:V < 79
        · by_cases h72_79:V < 75
          · by_cases h72_75:V < 73
            · have he:V = 72:=by omega
              subst V
              exact q26_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q26_73
              · have he:V = 74:=by omega
                subst V
                exact q26_74
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q26_75
              · have he:V = 76:=by omega
                subst V
                exact q26_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q26_77
              · have he:V = 78:=by omega
                subst V
                exact q26_78
        · by_cases h79_87:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q26_79
              · have he:V = 80:=by omega
                subst V
                exact q26_80
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q26_81
              · have he:V = 82:=by omega
                subst V
                exact q26_82
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q26_83
              · have he:V = 84:=by omega
                subst V
                exact q26_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q26_85
              · have he:V = 86:=by omega
                subst V
                exact q26_86
    · by_cases h87_117:V < 102
      · by_cases h87_102:V < 94
        · by_cases h87_94:V < 90
          · by_cases h87_90:V < 88
            · have he:V = 87:=by omega
              subst V
              exact q26_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q26_88
              · have he:V = 89:=by omega
                subst V
                exact q26_89
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q26_90
              · have he:V = 91:=by omega
                subst V
                exact q26_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q26_92
              · have he:V = 93:=by omega
                subst V
                exact q26_93
        · by_cases h94_102:V < 98
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q26_94
              · have he:V = 95:=by omega
                subst V
                exact q26_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q26_96
              · have he:V = 97:=by omega
                subst V
                exact q26_97
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q26_98
              · have he:V = 99:=by omega
                subst V
                exact q26_99
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q26_100
              · have he:V = 101:=by omega
                subst V
                exact q26_101
      · by_cases h102_117:V < 109
        · by_cases h102_109:V < 105
          · by_cases h102_105:V < 103
            · have he:V = 102:=by omega
              subst V
              exact q26_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q26_103
              · have he:V = 104:=by omega
                subst V
                exact q26_104
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q26_105
              · have he:V = 106:=by omega
                subst V
                exact q26_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q26_107
              · have he:V = 108:=by omega
                subst V
                exact q26_108
        · by_cases h109_117:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q26_109
              · have he:V = 110:=by omega
                subst V
                exact q26_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q26_111
              · have he:V = 112:=by omega
                subst V
                exact q26_112
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q26_113
              · have he:V = 114:=by omega
                subst V
                exact q26_114
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q26_115
              · have he:V = 116:=by omega
                subst V
                exact q26_116
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
