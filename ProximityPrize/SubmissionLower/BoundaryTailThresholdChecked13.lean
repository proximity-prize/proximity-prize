import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked12

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q13_0:ThresholdAt 13 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 0 0 (by decide +kernel)
  | exact S 13 0 1 (by decide +kernel)
  | exact S 13 0 2 (by decide +kernel)
  | exact S 13 0 3 (by decide +kernel)
  | exact S 13 0 4 (by decide +kernel)
  | exact S 13 0 5 (by decide +kernel)
theorem q13_1:ThresholdAt 13 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 1 0 (by decide +kernel)
  | exact S 13 1 1 (by decide +kernel)
  | exact S 13 1 2 (by decide +kernel)
  | exact S 13 1 3 (by decide +kernel)
  | exact S 13 1 4 (by decide +kernel)
  | exact S 13 1 5 (by decide +kernel)
theorem q13_2:ThresholdAt 13 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 2 0 (by decide +kernel)
  | exact S 13 2 1 (by decide +kernel)
  | exact S 13 2 2 (by decide +kernel)
  | exact S 13 2 3 (by decide +kernel)
  | exact S 13 2 4 (by decide +kernel)
  | exact S 13 2 5 (by decide +kernel)
theorem q13_3:ThresholdAt 13 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 3 0 (by decide +kernel)
  | exact S 13 3 1 (by decide +kernel)
  | exact S 13 3 2 (by decide +kernel)
  | exact S 13 3 3 (by decide +kernel)
  | exact S 13 3 4 (by decide +kernel)
  | exact S 13 3 5 (by decide +kernel)
theorem q13_4:ThresholdAt 13 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 4 0 (by decide +kernel)
  | exact S 13 4 1 (by decide +kernel)
  | exact S 13 4 2 (by decide +kernel)
  | exact S 13 4 3 (by decide +kernel)
  | exact S 13 4 4 (by decide +kernel)
  | exact S 13 4 5 (by decide +kernel)
theorem q13_5:ThresholdAt 13 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 5 0 (by decide +kernel)
  | exact S 13 5 1 (by decide +kernel)
  | exact S 13 5 2 (by decide +kernel)
  | exact S 13 5 3 (by decide +kernel)
  | exact S 13 5 4 (by decide +kernel)
  | exact S 13 5 5 (by decide +kernel)
theorem q13_6:ThresholdAt 13 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 6 0 (by decide +kernel)
  | exact S 13 6 1 (by decide +kernel)
  | exact S 13 6 2 (by decide +kernel)
  | exact S 13 6 3 (by decide +kernel)
  | exact S 13 6 4 (by decide +kernel)
  | exact S 13 6 5 (by decide +kernel)
theorem q13_7:ThresholdAt 13 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 7 0 (by decide +kernel)
  | exact S 13 7 1 (by decide +kernel)
  | exact S 13 7 2 (by decide +kernel)
  | exact S 13 7 3 (by decide +kernel)
  | exact S 13 7 4 (by decide +kernel)
  | exact S 13 7 5 (by decide +kernel)
theorem q13_8:ThresholdAt 13 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 8 0 (by decide +kernel)
  | exact S 13 8 1 (by decide +kernel)
  | exact S 13 8 2 (by decide +kernel)
  | exact S 13 8 3 (by decide +kernel)
  | exact S 13 8 4 (by decide +kernel)
  | exact S 13 8 5 (by decide +kernel)
theorem q13_9:ThresholdAt 13 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 9 0 (by decide +kernel)
  | exact S 13 9 1 (by decide +kernel)
  | exact S 13 9 2 (by decide +kernel)
  | exact S 13 9 3 (by decide +kernel)
  | exact S 13 9 4 (by decide +kernel)
  | exact S 13 9 5 (by decide +kernel)
theorem q13_10:ThresholdAt 13 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 10 0 (by decide +kernel)
  | exact S 13 10 1 (by decide +kernel)
  | exact S 13 10 2 (by decide +kernel)
  | exact S 13 10 3 (by decide +kernel)
  | exact S 13 10 4 (by decide +kernel)
  | exact S 13 10 5 (by decide +kernel)
theorem q13_11:ThresholdAt 13 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 11 0 (by decide +kernel)
  | exact S 13 11 1 (by decide +kernel)
  | exact S 13 11 2 (by decide +kernel)
  | exact S 13 11 3 (by decide +kernel)
  | exact S 13 11 4 (by decide +kernel)
  | exact S 13 11 5 (by decide +kernel)
theorem q13_12:ThresholdAt 13 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 12 0 (by decide +kernel)
  | exact S 13 12 1 (by decide +kernel)
  | exact S 13 12 2 (by decide +kernel)
  | exact S 13 12 3 (by decide +kernel)
  | exact S 13 12 4 (by decide +kernel)
  | exact S 13 12 5 (by decide +kernel)
theorem q13_13:ThresholdAt 13 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 13 0 (by decide +kernel)
  | exact S 13 13 1 (by decide +kernel)
  | exact S 13 13 2 (by decide +kernel)
  | exact S 13 13 3 (by decide +kernel)
  | exact S 13 13 4 (by decide +kernel)
  | exact S 13 13 5 (by decide +kernel)
theorem q13_14:ThresholdAt 13 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 14 0 (by decide +kernel)
  | exact S 13 14 1 (by decide +kernel)
  | exact S 13 14 2 (by decide +kernel)
  | exact S 13 14 3 (by decide +kernel)
  | exact S 13 14 4 (by decide +kernel)
  | exact S 13 14 5 (by decide +kernel)
theorem q13_15:ThresholdAt 13 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 15 0 (by decide +kernel)
  | exact S 13 15 1 (by decide +kernel)
  | exact S 13 15 2 (by decide +kernel)
  | exact S 13 15 3 (by decide +kernel)
  | exact S 13 15 4 (by decide +kernel)
  | exact S 13 15 5 (by decide +kernel)
theorem q13_16:ThresholdAt 13 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 16 0 (by decide +kernel)
  | exact S 13 16 1 (by decide +kernel)
  | exact S 13 16 2 (by decide +kernel)
  | exact S 13 16 3 (by decide +kernel)
  | exact S 13 16 4 (by decide +kernel)
  | exact S 13 16 5 (by decide +kernel)
theorem q13_17:ThresholdAt 13 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 17 0 (by decide +kernel)
  | exact S 13 17 1 (by decide +kernel)
  | exact S 13 17 2 (by decide +kernel)
  | exact S 13 17 3 (by decide +kernel)
  | exact S 13 17 4 (by decide +kernel)
  | exact S 13 17 5 (by decide +kernel)
theorem q13_18:ThresholdAt 13 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 18 0 (by decide +kernel)
  | exact S 13 18 1 (by decide +kernel)
  | exact S 13 18 2 (by decide +kernel)
  | exact S 13 18 3 (by decide +kernel)
  | exact S 13 18 4 (by decide +kernel)
  | exact S 13 18 5 (by decide +kernel)
theorem q13_19:ThresholdAt 13 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 19 0 (by decide +kernel)
  | exact S 13 19 1 (by decide +kernel)
  | exact S 13 19 2 (by decide +kernel)
  | exact S 13 19 3 (by decide +kernel)
  | exact S 13 19 4 (by decide +kernel)
  | exact S 13 19 5 (by decide +kernel)
theorem q13_20:ThresholdAt 13 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 20 0 (by decide +kernel)
  | exact S 13 20 1 (by decide +kernel)
  | exact S 13 20 2 (by decide +kernel)
  | exact S 13 20 3 (by decide +kernel)
  | exact S 13 20 4 (by decide +kernel)
  | exact S 13 20 5 (by decide +kernel)
theorem q13_21:ThresholdAt 13 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 21 0 (by decide +kernel)
  | exact S 13 21 1 (by decide +kernel)
  | exact S 13 21 2 (by decide +kernel)
  | exact S 13 21 3 (by decide +kernel)
  | exact S 13 21 4 (by decide +kernel)
  | exact S 13 21 5 (by decide +kernel)
theorem q13_22:ThresholdAt 13 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 22 0 (by decide +kernel)
  | exact S 13 22 1 (by decide +kernel)
  | exact S 13 22 2 (by decide +kernel)
  | exact S 13 22 3 (by decide +kernel)
  | exact S 13 22 4 (by decide +kernel)
  | exact S 13 22 5 (by decide +kernel)
theorem q13_23:ThresholdAt 13 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 23 0 (by decide +kernel)
  | exact S 13 23 1 (by decide +kernel)
  | exact S 13 23 2 (by decide +kernel)
  | exact S 13 23 3 (by decide +kernel)
  | exact S 13 23 4 (by decide +kernel)
  | exact S 13 23 5 (by decide +kernel)
theorem q13_24:ThresholdAt 13 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 24 0 (by decide +kernel)
  | exact S 13 24 1 (by decide +kernel)
  | exact S 13 24 2 (by decide +kernel)
  | exact S 13 24 3 (by decide +kernel)
  | exact S 13 24 4 (by decide +kernel)
  | exact S 13 24 5 (by decide +kernel)
theorem q13_25:ThresholdAt 13 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 25 0 (by decide +kernel)
  | exact S 13 25 1 (by decide +kernel)
  | exact S 13 25 2 (by decide +kernel)
  | exact S 13 25 3 (by decide +kernel)
  | exact S 13 25 4 (by decide +kernel)
  | exact S 13 25 5 (by decide +kernel)
theorem q13_26:ThresholdAt 13 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 26 0 (by decide +kernel)
  | exact S 13 26 1 (by decide +kernel)
  | exact S 13 26 2 (by decide +kernel)
  | exact S 13 26 3 (by decide +kernel)
  | exact S 13 26 4 (by decide +kernel)
  | exact S 13 26 5 (by decide +kernel)
theorem q13_27:ThresholdAt 13 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 27 0 (by decide +kernel)
  | exact S 13 27 1 (by decide +kernel)
  | exact S 13 27 2 (by decide +kernel)
  | exact S 13 27 3 (by decide +kernel)
  | exact S 13 27 4 (by decide +kernel)
  | exact S 13 27 5 (by decide +kernel)
theorem q13_28:ThresholdAt 13 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 28 0 (by decide +kernel)
  | exact S 13 28 1 (by decide +kernel)
  | exact S 13 28 2 (by decide +kernel)
  | exact S 13 28 3 (by decide +kernel)
  | exact S 13 28 4 (by decide +kernel)
  | exact S 13 28 5 (by decide +kernel)
theorem q13_29:ThresholdAt 13 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 29 0 (by decide +kernel)
  | exact S 13 29 1 (by decide +kernel)
  | exact S 13 29 2 (by decide +kernel)
  | exact S 13 29 3 (by decide +kernel)
  | exact S 13 29 4 (by decide +kernel)
  | exact S 13 29 5 (by decide +kernel)
theorem q13_30:ThresholdAt 13 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 30 0 (by decide +kernel)
  | exact S 13 30 1 (by decide +kernel)
  | exact S 13 30 2 (by decide +kernel)
  | exact S 13 30 3 (by decide +kernel)
  | exact S 13 30 4 (by decide +kernel)
  | exact S 13 30 5 (by decide +kernel)
theorem q13_31:ThresholdAt 13 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 31 0 (by decide +kernel)
  | exact S 13 31 1 (by decide +kernel)
  | exact S 13 31 2 (by decide +kernel)
  | exact S 13 31 3 (by decide +kernel)
  | exact S 13 31 4 (by decide +kernel)
  | exact S 13 31 5 (by decide +kernel)
theorem q13_32:ThresholdAt 13 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 32 0 (by decide +kernel)
  | exact S 13 32 1 (by decide +kernel)
  | exact S 13 32 2 (by decide +kernel)
  | exact S 13 32 3 (by decide +kernel)
  | exact S 13 32 4 (by decide +kernel)
  | exact S 13 32 5 (by decide +kernel)
theorem q13_33:ThresholdAt 13 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 33 0 (by decide +kernel)
  | exact S 13 33 1 (by decide +kernel)
  | exact S 13 33 2 (by decide +kernel)
  | exact S 13 33 3 (by decide +kernel)
  | exact S 13 33 4 (by decide +kernel)
  | exact S 13 33 5 (by decide +kernel)
theorem q13_34:ThresholdAt 13 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 34 0 (by decide +kernel)
  | exact S 13 34 1 (by decide +kernel)
  | exact S 13 34 2 (by decide +kernel)
  | exact S 13 34 3 (by decide +kernel)
  | exact S 13 34 4 (by decide +kernel)
  | exact S 13 34 5 (by decide +kernel)
theorem q13_35:ThresholdAt 13 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 35 0 (by decide +kernel)
  | exact S 13 35 1 (by decide +kernel)
  | exact S 13 35 2 (by decide +kernel)
  | exact S 13 35 3 (by decide +kernel)
  | exact S 13 35 4 (by decide +kernel)
  | exact S 13 35 5 (by decide +kernel)
theorem q13_36:ThresholdAt 13 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 36 0 (by decide +kernel)
  | exact S 13 36 1 (by decide +kernel)
  | exact S 13 36 2 (by decide +kernel)
  | exact S 13 36 3 (by decide +kernel)
  | exact S 13 36 4 (by decide +kernel)
  | exact S 13 36 5 (by decide +kernel)
theorem q13_37:ThresholdAt 13 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 37 0 (by decide +kernel)
  | exact S 13 37 1 (by decide +kernel)
  | exact S 13 37 2 (by decide +kernel)
  | exact S 13 37 3 (by decide +kernel)
  | exact S 13 37 4 (by decide +kernel)
  | exact S 13 37 5 (by decide +kernel)
theorem q13_38:ThresholdAt 13 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 38 0 (by decide +kernel)
  | exact S 13 38 1 (by decide +kernel)
  | exact S 13 38 2 (by decide +kernel)
  | exact S 13 38 3 (by decide +kernel)
  | exact S 13 38 4 (by decide +kernel)
  | exact S 13 38 5 (by decide +kernel)
theorem q13_39:ThresholdAt 13 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 39 0 (by decide +kernel)
  | exact S 13 39 1 (by decide +kernel)
  | exact S 13 39 2 (by decide +kernel)
  | exact S 13 39 3 (by decide +kernel)
  | exact S 13 39 4 (by decide +kernel)
  | exact S 13 39 5 (by decide +kernel)
theorem q13_40:ThresholdAt 13 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 40 0 (by decide +kernel)
  | exact S 13 40 1 (by decide +kernel)
  | exact S 13 40 2 (by decide +kernel)
  | exact S 13 40 3 (by decide +kernel)
  | exact S 13 40 4 (by decide +kernel)
  | exact S 13 40 5 (by decide +kernel)
theorem q13_41:ThresholdAt 13 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 41 0 (by decide +kernel)
  | exact S 13 41 1 (by decide +kernel)
  | exact S 13 41 2 (by decide +kernel)
  | exact S 13 41 3 (by decide +kernel)
  | exact S 13 41 4 (by decide +kernel)
  | exact S 13 41 5 (by decide +kernel)
theorem q13_42:ThresholdAt 13 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 42 0 (by decide +kernel)
  | exact S 13 42 1 (by decide +kernel)
  | exact S 13 42 2 (by decide +kernel)
  | exact S 13 42 3 (by decide +kernel)
  | exact S 13 42 4 (by decide +kernel)
  | exact S 13 42 5 (by decide +kernel)
theorem q13_43:ThresholdAt 13 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 43 0 (by decide +kernel)
  | exact S 13 43 1 (by decide +kernel)
  | exact S 13 43 2 (by decide +kernel)
  | exact S 13 43 3 (by decide +kernel)
  | exact S 13 43 4 (by decide +kernel)
  | exact S 13 43 5 (by decide +kernel)
theorem q13_44:ThresholdAt 13 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 44 0 (by decide +kernel)
  | exact S 13 44 1 (by decide +kernel)
  | exact S 13 44 2 (by decide +kernel)
  | exact S 13 44 3 (by decide +kernel)
  | exact S 13 44 4 (by decide +kernel)
  | exact S 13 44 5 (by decide +kernel)
theorem q13_45:ThresholdAt 13 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 45 0 (by decide +kernel)
  | exact S 13 45 1 (by decide +kernel)
  | exact S 13 45 2 (by decide +kernel)
  | exact S 13 45 3 (by decide +kernel)
  | exact S 13 45 4 (by decide +kernel)
  | exact S 13 45 5 (by decide +kernel)
theorem q13_46:ThresholdAt 13 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 46 0 (by decide +kernel)
  | exact S 13 46 1 (by decide +kernel)
  | exact S 13 46 2 (by decide +kernel)
  | exact S 13 46 3 (by decide +kernel)
  | exact S 13 46 4 (by decide +kernel)
  | exact S 13 46 5 (by decide +kernel)
theorem q13_47:ThresholdAt 13 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 47 0 (by decide +kernel)
  | exact S 13 47 1 (by decide +kernel)
  | exact S 13 47 2 (by decide +kernel)
  | exact S 13 47 3 (by decide +kernel)
  | exact S 13 47 4 (by decide +kernel)
  | exact S 13 47 5 (by decide +kernel)
theorem q13_48:ThresholdAt 13 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 48 0 (by decide +kernel)
  | exact S 13 48 1 (by decide +kernel)
  | exact S 13 48 2 (by decide +kernel)
  | exact S 13 48 3 (by decide +kernel)
  | exact S 13 48 4 (by decide +kernel)
  | exact S 13 48 5 (by decide +kernel)
theorem q13_49:ThresholdAt 13 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 49 0 (by decide +kernel)
  | exact S 13 49 1 (by decide +kernel)
  | exact S 13 49 2 (by decide +kernel)
  | exact S 13 49 3 (by decide +kernel)
  | exact S 13 49 4 (by decide +kernel)
  | exact S 13 49 5 (by decide +kernel)
theorem q13_50:ThresholdAt 13 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 50 0 (by decide +kernel)
  | exact S 13 50 1 (by decide +kernel)
  | exact S 13 50 2 (by decide +kernel)
  | exact S 13 50 3 (by decide +kernel)
  | exact S 13 50 4 (by decide +kernel)
  | exact S 13 50 5 (by decide +kernel)
theorem q13_51:ThresholdAt 13 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 51 0 (by decide +kernel)
  | exact S 13 51 1 (by decide +kernel)
  | exact S 13 51 2 (by decide +kernel)
  | exact S 13 51 3 (by decide +kernel)
  | exact S 13 51 4 (by decide +kernel)
  | exact S 13 51 5 (by decide +kernel)
theorem q13_52:ThresholdAt 13 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 52 0 (by decide +kernel)
  | exact S 13 52 1 (by decide +kernel)
  | exact S 13 52 2 (by decide +kernel)
  | exact S 13 52 3 (by decide +kernel)
  | exact S 13 52 4 (by decide +kernel)
  | exact S 13 52 5 (by decide +kernel)
theorem q13_53:ThresholdAt 13 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 53 0 (by decide +kernel)
  | exact S 13 53 1 (by decide +kernel)
  | exact S 13 53 2 (by decide +kernel)
  | exact S 13 53 3 (by decide +kernel)
  | exact S 13 53 4 (by decide +kernel)
  | exact S 13 53 5 (by decide +kernel)
theorem q13_54:ThresholdAt 13 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 54 0 (by decide +kernel)
  | exact S 13 54 1 (by decide +kernel)
  | exact S 13 54 2 (by decide +kernel)
  | exact S 13 54 3 (by decide +kernel)
  | exact S 13 54 4 (by decide +kernel)
  | exact S 13 54 5 (by decide +kernel)
theorem q13_55:ThresholdAt 13 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 55 0 (by decide +kernel)
  | exact S 13 55 1 (by decide +kernel)
  | exact S 13 55 2 (by decide +kernel)
  | exact S 13 55 3 (by decide +kernel)
  | exact S 13 55 4 (by decide +kernel)
  | exact S 13 55 5 (by decide +kernel)
theorem q13_56:ThresholdAt 13 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 56 0 (by decide +kernel)
  | exact S 13 56 1 (by decide +kernel)
  | exact S 13 56 2 (by decide +kernel)
  | exact S 13 56 3 (by decide +kernel)
  | exact S 13 56 4 (by decide +kernel)
  | exact S 13 56 5 (by decide +kernel)
theorem q13_57:ThresholdAt 13 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 57 0 (by decide +kernel)
  | exact S 13 57 1 (by decide +kernel)
  | exact S 13 57 2 (by decide +kernel)
  | exact S 13 57 3 (by decide +kernel)
  | exact S 13 57 4 (by decide +kernel)
  | exact S 13 57 5 (by decide +kernel)
theorem q13_58:ThresholdAt 13 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 58 0 (by decide +kernel)
  | exact S 13 58 1 (by decide +kernel)
  | exact S 13 58 2 (by decide +kernel)
  | exact S 13 58 3 (by decide +kernel)
  | exact S 13 58 4 (by decide +kernel)
  | exact S 13 58 5 (by decide +kernel)
theorem q13_59:ThresholdAt 13 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 59 0 (by decide +kernel)
  | exact S 13 59 1 (by decide +kernel)
  | exact S 13 59 2 (by decide +kernel)
  | exact S 13 59 3 (by decide +kernel)
  | exact S 13 59 4 (by decide +kernel)
  | exact S 13 59 5 (by decide +kernel)
theorem q13_60:ThresholdAt 13 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 60 0 (by decide +kernel)
  | exact S 13 60 1 (by decide +kernel)
  | exact S 13 60 2 (by decide +kernel)
  | exact S 13 60 3 (by decide +kernel)
  | exact S 13 60 4 (by decide +kernel)
  | exact S 13 60 5 (by decide +kernel)
theorem q13_61:ThresholdAt 13 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 61 0 (by decide +kernel)
  | exact S 13 61 1 (by decide +kernel)
  | exact S 13 61 2 (by decide +kernel)
  | exact S 13 61 3 (by decide +kernel)
  | exact S 13 61 4 (by decide +kernel)
  | exact S 13 61 5 (by decide +kernel)
theorem q13_62:ThresholdAt 13 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 62 0 (by decide +kernel)
  | exact S 13 62 1 (by decide +kernel)
  | exact S 13 62 2 (by decide +kernel)
  | exact S 13 62 3 (by decide +kernel)
  | exact S 13 62 4 (by decide +kernel)
  | exact S 13 62 5 (by decide +kernel)
theorem q13_63:ThresholdAt 13 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 63 0 (by decide +kernel)
  | exact S 13 63 1 (by decide +kernel)
  | exact S 13 63 2 (by decide +kernel)
  | exact S 13 63 3 (by decide +kernel)
  | exact S 13 63 4 (by decide +kernel)
  | exact S 13 63 5 (by decide +kernel)
theorem q13_64:ThresholdAt 13 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 64 0 (by decide +kernel)
  | exact S 13 64 1 (by decide +kernel)
  | exact S 13 64 2 (by decide +kernel)
  | exact S 13 64 3 (by decide +kernel)
  | exact S 13 64 4 (by decide +kernel)
  | exact S 13 64 5 (by decide +kernel)
theorem q13_65:ThresholdAt 13 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 65 0 (by decide +kernel)
  | exact S 13 65 1 (by decide +kernel)
  | exact S 13 65 2 (by decide +kernel)
  | exact S 13 65 3 (by decide +kernel)
  | exact S 13 65 4 (by decide +kernel)
  | exact S 13 65 5 (by decide +kernel)
theorem q13_66:ThresholdAt 13 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 66 0 (by decide +kernel)
  | exact S 13 66 1 (by decide +kernel)
  | exact S 13 66 2 (by decide +kernel)
  | exact S 13 66 3 (by decide +kernel)
  | exact S 13 66 4 (by decide +kernel)
  | exact S 13 66 5 (by decide +kernel)
theorem q13_67:ThresholdAt 13 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 67 0 (by decide +kernel)
  | exact S 13 67 1 (by decide +kernel)
  | exact S 13 67 2 (by decide +kernel)
  | exact S 13 67 3 (by decide +kernel)
  | exact S 13 67 4 (by decide +kernel)
  | exact S 13 67 5 (by decide +kernel)
theorem q13_68:ThresholdAt 13 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 68 0 (by decide +kernel)
  | exact S 13 68 1 (by decide +kernel)
  | exact S 13 68 2 (by decide +kernel)
  | exact S 13 68 3 (by decide +kernel)
  | exact S 13 68 4 (by decide +kernel)
  | exact S 13 68 5 (by decide +kernel)
theorem q13_69:ThresholdAt 13 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 69 0 (by decide +kernel)
  | exact S 13 69 1 (by decide +kernel)
  | exact S 13 69 2 (by decide +kernel)
  | exact S 13 69 3 (by decide +kernel)
  | exact S 13 69 4 (by decide +kernel)
  | exact S 13 69 5 (by decide +kernel)
theorem q13_70:ThresholdAt 13 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 70 0 (by decide +kernel)
  | exact S 13 70 1 (by decide +kernel)
  | exact S 13 70 2 (by decide +kernel)
  | exact S 13 70 3 (by decide +kernel)
  | exact S 13 70 4 (by decide +kernel)
  | exact S 13 70 5 (by decide +kernel)
theorem q13_71:ThresholdAt 13 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 71 0 (by decide +kernel)
  | exact S 13 71 1 (by decide +kernel)
  | exact S 13 71 2 (by decide +kernel)
  | exact S 13 71 3 (by decide +kernel)
  | exact S 13 71 4 (by decide +kernel)
  | exact S 13 71 5 (by decide +kernel)
theorem q13_72:ThresholdAt 13 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 72 0 (by decide +kernel)
  | exact S 13 72 1 (by decide +kernel)
  | exact S 13 72 2 (by decide +kernel)
  | exact S 13 72 3 (by decide +kernel)
  | exact S 13 72 4 (by decide +kernel)
  | exact S 13 72 5 (by decide +kernel)
theorem q13_73:ThresholdAt 13 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 73 0 (by decide +kernel)
  | exact S 13 73 1 (by decide +kernel)
  | exact S 13 73 2 (by decide +kernel)
  | exact S 13 73 3 (by decide +kernel)
  | exact S 13 73 4 (by decide +kernel)
  | exact S 13 73 5 (by decide +kernel)
theorem q13_74:ThresholdAt 13 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 74 0 (by decide +kernel)
  | exact S 13 74 1 (by decide +kernel)
  | exact S 13 74 2 (by decide +kernel)
  | exact S 13 74 3 (by decide +kernel)
  | exact S 13 74 4 (by decide +kernel)
  | exact S 13 74 5 (by decide +kernel)
theorem q13_75:ThresholdAt 13 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 75 0 (by decide +kernel)
  | exact S 13 75 1 (by decide +kernel)
  | exact S 13 75 2 (by decide +kernel)
  | exact S 13 75 3 (by decide +kernel)
  | exact S 13 75 4 (by decide +kernel)
  | exact S 13 75 5 (by decide +kernel)
theorem q13_76:ThresholdAt 13 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 76 0 (by decide +kernel)
  | exact S 13 76 1 (by decide +kernel)
  | exact S 13 76 2 (by decide +kernel)
  | exact S 13 76 3 (by decide +kernel)
  | exact S 13 76 4 (by decide +kernel)
  | exact S 13 76 5 (by decide +kernel)
theorem q13_77:ThresholdAt 13 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 77 0 (by decide +kernel)
  | exact S 13 77 1 (by decide +kernel)
  | exact S 13 77 2 (by decide +kernel)
  | exact S 13 77 3 (by decide +kernel)
  | exact S 13 77 4 (by decide +kernel)
  | exact S 13 77 5 (by decide +kernel)
theorem q13_78:ThresholdAt 13 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 78 0 (by decide +kernel)
  | exact S 13 78 1 (by decide +kernel)
  | exact S 13 78 2 (by decide +kernel)
  | exact S 13 78 3 (by decide +kernel)
  | exact S 13 78 4 (by decide +kernel)
  | exact S 13 78 5 (by decide +kernel)
theorem q13_79:ThresholdAt 13 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 79 0 (by decide +kernel)
  | exact S 13 79 1 (by decide +kernel)
  | exact S 13 79 2 (by decide +kernel)
  | exact S 13 79 3 (by decide +kernel)
  | exact S 13 79 4 (by decide +kernel)
  | exact S 13 79 5 (by decide +kernel)
theorem q13_80:ThresholdAt 13 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 80 0 (by decide +kernel)
  | exact S 13 80 1 (by decide +kernel)
  | exact S 13 80 2 (by decide +kernel)
  | exact S 13 80 3 (by decide +kernel)
  | exact S 13 80 4 (by decide +kernel)
  | exact S 13 80 5 (by decide +kernel)
theorem q13_81:ThresholdAt 13 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 81 0 (by decide +kernel)
  | exact S 13 81 1 (by decide +kernel)
  | exact S 13 81 2 (by decide +kernel)
  | exact S 13 81 3 (by decide +kernel)
  | exact S 13 81 4 (by decide +kernel)
  | exact S 13 81 5 (by decide +kernel)
theorem q13_82:ThresholdAt 13 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 82 0 (by decide +kernel)
  | exact S 13 82 1 (by decide +kernel)
  | exact S 13 82 2 (by decide +kernel)
  | exact S 13 82 3 (by decide +kernel)
  | exact S 13 82 4 (by decide +kernel)
  | exact S 13 82 5 (by decide +kernel)
theorem q13_83:ThresholdAt 13 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 83 0 (by decide +kernel)
  | exact S 13 83 1 (by decide +kernel)
  | exact S 13 83 2 (by decide +kernel)
  | exact S 13 83 3 (by decide +kernel)
  | exact S 13 83 4 (by decide +kernel)
  | exact S 13 83 5 (by decide +kernel)
theorem q13_84:ThresholdAt 13 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 84 0 (by decide +kernel)
  | exact S 13 84 1 (by decide +kernel)
  | exact S 13 84 2 (by decide +kernel)
  | exact S 13 84 3 (by decide +kernel)
  | exact S 13 84 4 (by decide +kernel)
  | exact S 13 84 5 (by decide +kernel)
theorem q13_85:ThresholdAt 13 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 85 0 (by decide +kernel)
  | exact S 13 85 1 (by decide +kernel)
  | exact S 13 85 2 (by decide +kernel)
  | exact S 13 85 3 (by decide +kernel)
  | exact S 13 85 4 (by decide +kernel)
  | exact S 13 85 5 (by decide +kernel)
theorem q13_86:ThresholdAt 13 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 86 0 (by decide +kernel)
  | exact S 13 86 1 (by decide +kernel)
  | exact S 13 86 2 (by decide +kernel)
  | exact S 13 86 3 (by decide +kernel)
  | exact S 13 86 4 (by decide +kernel)
  | exact S 13 86 5 (by decide +kernel)
theorem q13_87:ThresholdAt 13 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 87 0 (by decide +kernel)
  | exact S 13 87 1 (by decide +kernel)
  | exact S 13 87 2 (by decide +kernel)
  | exact S 13 87 3 (by decide +kernel)
  | exact S 13 87 4 (by decide +kernel)
  | exact S 13 87 5 (by decide +kernel)
theorem q13_88:ThresholdAt 13 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 88 0 (by decide +kernel)
  | exact S 13 88 1 (by decide +kernel)
  | exact S 13 88 2 (by decide +kernel)
  | exact S 13 88 3 (by decide +kernel)
  | exact S 13 88 4 (by decide +kernel)
  | exact S 13 88 5 (by decide +kernel)
theorem q13_89:ThresholdAt 13 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 89 0 (by decide +kernel)
  | exact S 13 89 1 (by decide +kernel)
  | exact S 13 89 2 (by decide +kernel)
  | exact S 13 89 3 (by decide +kernel)
  | exact S 13 89 4 (by decide +kernel)
  | exact S 13 89 5 (by decide +kernel)
theorem q13_90:ThresholdAt 13 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 90 0 (by decide +kernel)
  | exact S 13 90 1 (by decide +kernel)
  | exact S 13 90 2 (by decide +kernel)
  | exact S 13 90 3 (by decide +kernel)
  | exact S 13 90 4 (by decide +kernel)
  | exact S 13 90 5 (by decide +kernel)
theorem q13_91:ThresholdAt 13 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 91 0 (by decide +kernel)
  | exact S 13 91 1 (by decide +kernel)
  | exact S 13 91 2 (by decide +kernel)
  | exact S 13 91 3 (by decide +kernel)
  | exact S 13 91 4 (by decide +kernel)
  | exact S 13 91 5 (by decide +kernel)
theorem q13_92:ThresholdAt 13 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 92 0 (by decide +kernel)
  | exact S 13 92 1 (by decide +kernel)
  | exact S 13 92 2 (by decide +kernel)
  | exact S 13 92 3 (by decide +kernel)
  | exact S 13 92 4 (by decide +kernel)
  | exact S 13 92 5 (by decide +kernel)
theorem q13_93:ThresholdAt 13 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 93 0 (by decide +kernel)
  | exact S 13 93 1 (by decide +kernel)
  | exact S 13 93 2 (by decide +kernel)
  | exact S 13 93 3 (by decide +kernel)
  | exact S 13 93 4 (by decide +kernel)
  | exact S 13 93 5 (by decide +kernel)
theorem q13_94:ThresholdAt 13 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 94 0 (by decide +kernel)
  | exact S 13 94 1 (by decide +kernel)
  | exact S 13 94 2 (by decide +kernel)
  | exact S 13 94 3 (by decide +kernel)
  | exact S 13 94 4 (by decide +kernel)
  | exact S 13 94 5 (by decide +kernel)
theorem q13_95:ThresholdAt 13 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 95 0 (by decide +kernel)
  | exact S 13 95 1 (by decide +kernel)
  | exact S 13 95 2 (by decide +kernel)
  | exact S 13 95 3 (by decide +kernel)
  | exact S 13 95 4 (by decide +kernel)
  | exact S 13 95 5 (by decide +kernel)
theorem q13_96:ThresholdAt 13 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 96 0 (by decide +kernel)
  | exact S 13 96 1 (by decide +kernel)
  | exact S 13 96 2 (by decide +kernel)
  | exact S 13 96 3 (by decide +kernel)
  | exact S 13 96 4 (by decide +kernel)
  | exact S 13 96 5 (by decide +kernel)
theorem q13_97:ThresholdAt 13 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 97 0 (by decide +kernel)
  | exact S 13 97 1 (by decide +kernel)
  | exact S 13 97 2 (by decide +kernel)
  | exact S 13 97 3 (by decide +kernel)
  | exact S 13 97 4 (by decide +kernel)
  | exact S 13 97 5 (by decide +kernel)
theorem q13_98:ThresholdAt 13 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 98 0 (by decide +kernel)
  | exact S 13 98 1 (by decide +kernel)
  | exact S 13 98 2 (by decide +kernel)
  | exact S 13 98 3 (by decide +kernel)
  | exact S 13 98 4 (by decide +kernel)
  | exact S 13 98 5 (by decide +kernel)
theorem q13_99:ThresholdAt 13 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 99 0 (by decide +kernel)
  | exact S 13 99 1 (by decide +kernel)
  | exact S 13 99 2 (by decide +kernel)
  | exact S 13 99 3 (by decide +kernel)
  | exact S 13 99 4 (by decide +kernel)
  | exact S 13 99 5 (by decide +kernel)
theorem q13_100:ThresholdAt 13 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 100 0 (by decide +kernel)
  | exact S 13 100 1 (by decide +kernel)
  | exact S 13 100 2 (by decide +kernel)
  | exact S 13 100 3 (by decide +kernel)
  | exact S 13 100 4 (by decide +kernel)
  | exact S 13 100 5 (by decide +kernel)
theorem q13_101:ThresholdAt 13 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 101 0 (by decide +kernel)
  | exact S 13 101 1 (by decide +kernel)
  | exact S 13 101 2 (by decide +kernel)
  | exact S 13 101 3 (by decide +kernel)
  | exact S 13 101 4 (by decide +kernel)
  | exact S 13 101 5 (by decide +kernel)
theorem q13_102:ThresholdAt 13 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 102 0 (by decide +kernel)
  | exact S 13 102 1 (by decide +kernel)
  | exact S 13 102 2 (by decide +kernel)
  | exact S 13 102 3 (by decide +kernel)
  | exact S 13 102 4 (by decide +kernel)
  | exact S 13 102 5 (by decide +kernel)
theorem q13_103:ThresholdAt 13 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 103 0 (by decide +kernel)
  | exact S 13 103 1 (by decide +kernel)
  | exact S 13 103 2 (by decide +kernel)
  | exact S 13 103 3 (by decide +kernel)
  | exact S 13 103 4 (by decide +kernel)
  | exact S 13 103 5 (by decide +kernel)
theorem q13_104:ThresholdAt 13 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 104 0 (by decide +kernel)
  | exact S 13 104 1 (by decide +kernel)
  | exact S 13 104 2 (by decide +kernel)
  | exact S 13 104 3 (by decide +kernel)
  | exact S 13 104 4 (by decide +kernel)
  | exact S 13 104 5 (by decide +kernel)
theorem q13_105:ThresholdAt 13 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 105 0 (by decide +kernel)
  | exact S 13 105 1 (by decide +kernel)
  | exact S 13 105 2 (by decide +kernel)
  | exact S 13 105 3 (by decide +kernel)
  | exact S 13 105 4 (by decide +kernel)
  | exact S 13 105 5 (by decide +kernel)
theorem q13_106:ThresholdAt 13 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 106 0 (by decide +kernel)
  | exact S 13 106 1 (by decide +kernel)
  | exact S 13 106 2 (by decide +kernel)
  | exact S 13 106 3 (by decide +kernel)
  | exact S 13 106 4 (by decide +kernel)
  | exact S 13 106 5 (by decide +kernel)
theorem q13_107:ThresholdAt 13 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 107 0 (by decide +kernel)
  | exact S 13 107 1 (by decide +kernel)
  | exact S 13 107 2 (by decide +kernel)
  | exact S 13 107 3 (by decide +kernel)
  | exact S 13 107 4 (by decide +kernel)
  | exact S 13 107 5 (by decide +kernel)
theorem q13_108:ThresholdAt 13 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 108 0 (by decide +kernel)
  | exact S 13 108 1 (by decide +kernel)
  | exact S 13 108 2 (by decide +kernel)
  | exact S 13 108 3 (by decide +kernel)
  | exact S 13 108 4 (by decide +kernel)
  | exact S 13 108 5 (by decide +kernel)
theorem q13_109:ThresholdAt 13 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 109 0 (by decide +kernel)
  | exact S 13 109 1 (by decide +kernel)
  | exact S 13 109 2 (by decide +kernel)
  | exact S 13 109 3 (by decide +kernel)
  | exact S 13 109 4 (by decide +kernel)
  | exact S 13 109 5 (by decide +kernel)
theorem q13_110:ThresholdAt 13 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 110 0 (by decide +kernel)
  | exact S 13 110 1 (by decide +kernel)
  | exact S 13 110 2 (by decide +kernel)
  | exact S 13 110 3 (by decide +kernel)
  | exact S 13 110 4 (by decide +kernel)
  | exact S 13 110 5 (by decide +kernel)
theorem q13_111:ThresholdAt 13 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 111 0 (by decide +kernel)
  | exact S 13 111 1 (by decide +kernel)
  | exact S 13 111 2 (by decide +kernel)
  | exact S 13 111 3 (by decide +kernel)
  | exact S 13 111 4 (by decide +kernel)
  | exact S 13 111 5 (by decide +kernel)
theorem q13_112:ThresholdAt 13 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 112 0 (by decide +kernel)
  | exact S 13 112 1 (by decide +kernel)
  | exact S 13 112 2 (by decide +kernel)
  | exact S 13 112 3 (by decide +kernel)
  | exact S 13 112 4 (by decide +kernel)
  | exact S 13 112 5 (by decide +kernel)
theorem q13_113:ThresholdAt 13 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 113 0 (by decide +kernel)
  | exact S 13 113 1 (by decide +kernel)
  | exact S 13 113 2 (by decide +kernel)
  | exact S 13 113 3 (by decide +kernel)
  | exact S 13 113 4 (by decide +kernel)
  | exact S 13 113 5 (by decide +kernel)
theorem q13_114:ThresholdAt 13 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 114 0 (by decide +kernel)
  | exact S 13 114 1 (by decide +kernel)
  | exact S 13 114 2 (by decide +kernel)
  | exact S 13 114 3 (by decide +kernel)
  | exact S 13 114 4 (by decide +kernel)
  | exact S 13 114 5 (by decide +kernel)
theorem q13_115:ThresholdAt 13 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 115 0 (by decide +kernel)
  | exact S 13 115 1 (by decide +kernel)
  | exact S 13 115 2 (by decide +kernel)
  | exact S 13 115 3 (by decide +kernel)
  | exact S 13 115 4 (by decide +kernel)
  | exact S 13 115 5 (by decide +kernel)
theorem q13_116:ThresholdAt 13 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 116 0 (by decide +kernel)
  | exact S 13 116 1 (by decide +kernel)
  | exact S 13 116 2 (by decide +kernel)
  | exact S 13 116 3 (by decide +kernel)
  | exact S 13 116 4 (by decide +kernel)
  | exact S 13 116 5 (by decide +kernel)
theorem q13_117:ThresholdAt 13 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 117 0 (by decide +kernel)
  | exact S 13 117 1 (by decide +kernel)
  | exact S 13 117 2 (by decide +kernel)
  | exact S 13 117 3 (by decide +kernel)
  | exact S 13 117 4 (by decide +kernel)
  | exact S 13 117 5 (by decide +kernel)
theorem q13_118:ThresholdAt 13 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 118 0 (by decide +kernel)
  | exact S 13 118 1 (by decide +kernel)
  | exact S 13 118 2 (by decide +kernel)
  | exact S 13 118 3 (by decide +kernel)
  | exact S 13 118 4 (by decide +kernel)
  | exact S 13 118 5 (by decide +kernel)
theorem q13_119:ThresholdAt 13 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 119 0 (by decide +kernel)
  | exact S 13 119 1 (by decide +kernel)
  | exact S 13 119 2 (by decide +kernel)
  | exact S 13 119 3 (by decide +kernel)
  | exact S 13 119 4 (by decide +kernel)
  | exact S 13 119 5 (by decide +kernel)
theorem q13_120:ThresholdAt 13 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 120 0 (by decide +kernel)
  | exact S 13 120 1 (by decide +kernel)
  | exact S 13 120 2 (by decide +kernel)
  | exact S 13 120 3 (by decide +kernel)
  | exact S 13 120 4 (by decide +kernel)
  | exact S 13 120 5 (by decide +kernel)
theorem q13_121:ThresholdAt 13 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 121 0 (by decide +kernel)
  | exact S 13 121 1 (by decide +kernel)
  | exact S 13 121 2 (by decide +kernel)
  | exact S 13 121 3 (by decide +kernel)
  | exact S 13 121 4 (by decide +kernel)
  | exact S 13 121 5 (by decide +kernel)
theorem q13_122:ThresholdAt 13 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 122 0 (by decide +kernel)
  | exact S 13 122 1 (by decide +kernel)
  | exact S 13 122 2 (by decide +kernel)
  | exact S 13 122 3 (by decide +kernel)
  | exact S 13 122 4 (by decide +kernel)
  | exact S 13 122 5 (by decide +kernel)
theorem q13_123:ThresholdAt 13 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 123 0 (by decide +kernel)
  | exact S 13 123 1 (by decide +kernel)
  | exact S 13 123 2 (by decide +kernel)
  | exact S 13 123 3 (by decide +kernel)
  | exact S 13 123 4 (by decide +kernel)
  | exact S 13 123 5 (by decide +kernel)
theorem q13_124:ThresholdAt 13 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 124 0 (by decide +kernel)
  | exact S 13 124 1 (by decide +kernel)
  | exact S 13 124 2 (by decide +kernel)
  | exact S 13 124 3 (by decide +kernel)
  | exact S 13 124 4 (by decide +kernel)
  | exact S 13 124 5 (by decide +kernel)
theorem q13_125:ThresholdAt 13 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 125 0 (by decide +kernel)
  | exact S 13 125 1 (by decide +kernel)
  | exact S 13 125 2 (by decide +kernel)
  | exact S 13 125 3 (by decide +kernel)
  | exact S 13 125 4 (by decide +kernel)
  | exact S 13 125 5 (by decide +kernel)
theorem q13_126:ThresholdAt 13 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 126 0 (by decide +kernel)
  | exact S 13 126 1 (by decide +kernel)
  | exact S 13 126 2 (by decide +kernel)
  | exact S 13 126 3 (by decide +kernel)
  | exact S 13 126 4 (by decide +kernel)
  | exact S 13 126 5 (by decide +kernel)
theorem q13_127:ThresholdAt 13 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 127 0 (by decide +kernel)
  | exact S 13 127 1 (by decide +kernel)
  | exact S 13 127 2 (by decide +kernel)
  | exact S 13 127 3 (by decide +kernel)
  | exact S 13 127 4 (by decide +kernel)
  | exact S 13 127 5 (by decide +kernel)
theorem q13_128:ThresholdAt 13 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 128 0 (by decide +kernel)
  | exact S 13 128 1 (by decide +kernel)
  | exact S 13 128 2 (by decide +kernel)
  | exact S 13 128 3 (by decide +kernel)
  | exact S 13 128 4 (by decide +kernel)
  | exact S 13 128 5 (by decide +kernel)
theorem q13_129:ThresholdAt 13 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 13 129 0 (by decide +kernel)
  | exact S 13 129 1 (by decide +kernel)
  | exact S 13 129 2 (by decide +kernel)
  | exact S 13 129 3 (by decide +kernel)
  | exact S 13 129 4 (by decide +kernel)
  | exact S 13 129 5 (by decide +kernel)
theorem checkedR13:∀ V ∈ List.range 130,ThresholdAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0_130:V < 65
  · by_cases h0_65:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q13_0
              · have he:V = 1:=by omega
                subst V
                exact q13_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q13_2
              · have he:V = 3:=by omega
                subst V
                exact q13_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q13_4
              · have he:V = 5:=by omega
                subst V
                exact q13_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q13_6
              · have he:V = 7:=by omega
                subst V
                exact q13_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q13_8
              · have he:V = 9:=by omega
                subst V
                exact q13_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q13_10
              · have he:V = 11:=by omega
                subst V
                exact q13_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q13_12
              · have he:V = 13:=by omega
                subst V
                exact q13_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q13_14
              · have he:V = 15:=by omega
                subst V
                exact q13_15
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q13_16
              · have he:V = 17:=by omega
                subst V
                exact q13_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q13_18
              · have he:V = 19:=by omega
                subst V
                exact q13_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q13_20
              · have he:V = 21:=by omega
                subst V
                exact q13_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q13_22
              · have he:V = 23:=by omega
                subst V
                exact q13_23
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q13_24
              · have he:V = 25:=by omega
                subst V
                exact q13_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q13_26
              · have he:V = 27:=by omega
                subst V
                exact q13_27
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q13_28
              · have he:V = 29:=by omega
                subst V
                exact q13_29
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q13_30
              · have he:V = 31:=by omega
                subst V
                exact q13_31
    · by_cases h32_65:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q13_32
              · have he:V = 33:=by omega
                subst V
                exact q13_33
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q13_34
              · have he:V = 35:=by omega
                subst V
                exact q13_35
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q13_36
              · have he:V = 37:=by omega
                subst V
                exact q13_37
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q13_38
              · have he:V = 39:=by omega
                subst V
                exact q13_39
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q13_40
              · have he:V = 41:=by omega
                subst V
                exact q13_41
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q13_42
              · have he:V = 43:=by omega
                subst V
                exact q13_43
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q13_44
              · have he:V = 45:=by omega
                subst V
                exact q13_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q13_46
              · have he:V = 47:=by omega
                subst V
                exact q13_47
      · by_cases h48_65:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q13_48
              · have he:V = 49:=by omega
                subst V
                exact q13_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q13_50
              · have he:V = 51:=by omega
                subst V
                exact q13_51
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q13_52
              · have he:V = 53:=by omega
                subst V
                exact q13_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q13_54
              · have he:V = 55:=by omega
                subst V
                exact q13_55
        · by_cases h56_65:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q13_56
              · have he:V = 57:=by omega
                subst V
                exact q13_57
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q13_58
              · have he:V = 59:=by omega
                subst V
                exact q13_59
          · by_cases h60_65:V < 62
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q13_60
              · have he:V = 61:=by omega
                subst V
                exact q13_61
            · by_cases h62_65:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q13_62
              · by_cases h63_65:V < 64
                · have he:V = 63:=by omega
                  subst V
                  exact q13_63
                · have he:V = 64:=by omega
                  subst V
                  exact q13_64
  · by_cases h65_130:V < 97
    · by_cases h65_97:V < 81
      · by_cases h65_81:V < 73
        · by_cases h65_73:V < 69
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q13_65
              · have he:V = 66:=by omega
                subst V
                exact q13_66
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q13_67
              · have he:V = 68:=by omega
                subst V
                exact q13_68
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q13_69
              · have he:V = 70:=by omega
                subst V
                exact q13_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q13_71
              · have he:V = 72:=by omega
                subst V
                exact q13_72
        · by_cases h73_81:V < 77
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q13_73
              · have he:V = 74:=by omega
                subst V
                exact q13_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q13_75
              · have he:V = 76:=by omega
                subst V
                exact q13_76
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q13_77
              · have he:V = 78:=by omega
                subst V
                exact q13_78
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q13_79
              · have he:V = 80:=by omega
                subst V
                exact q13_80
      · by_cases h81_97:V < 89
        · by_cases h81_89:V < 85
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q13_81
              · have he:V = 82:=by omega
                subst V
                exact q13_82
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q13_83
              · have he:V = 84:=by omega
                subst V
                exact q13_84
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q13_85
              · have he:V = 86:=by omega
                subst V
                exact q13_86
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q13_87
              · have he:V = 88:=by omega
                subst V
                exact q13_88
        · by_cases h89_97:V < 93
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q13_89
              · have he:V = 90:=by omega
                subst V
                exact q13_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q13_91
              · have he:V = 92:=by omega
                subst V
                exact q13_92
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q13_93
              · have he:V = 94:=by omega
                subst V
                exact q13_94
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q13_95
              · have he:V = 96:=by omega
                subst V
                exact q13_96
    · by_cases h97_130:V < 113
      · by_cases h97_113:V < 105
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q13_97
              · have he:V = 98:=by omega
                subst V
                exact q13_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q13_99
              · have he:V = 100:=by omega
                subst V
                exact q13_100
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q13_101
              · have he:V = 102:=by omega
                subst V
                exact q13_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q13_103
              · have he:V = 104:=by omega
                subst V
                exact q13_104
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q13_105
              · have he:V = 106:=by omega
                subst V
                exact q13_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q13_107
              · have he:V = 108:=by omega
                subst V
                exact q13_108
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q13_109
              · have he:V = 110:=by omega
                subst V
                exact q13_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q13_111
              · have he:V = 112:=by omega
                subst V
                exact q13_112
      · by_cases h113_130:V < 121
        · by_cases h113_121:V < 117
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q13_113
              · have he:V = 114:=by omega
                subst V
                exact q13_114
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q13_115
              · have he:V = 116:=by omega
                subst V
                exact q13_116
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q13_117
              · have he:V = 118:=by omega
                subst V
                exact q13_118
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q13_119
              · have he:V = 120:=by omega
                subst V
                exact q13_120
        · by_cases h121_130:V < 125
          · by_cases h121_125:V < 123
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q13_121
              · have he:V = 122:=by omega
                subst V
                exact q13_122
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q13_123
              · have he:V = 124:=by omega
                subst V
                exact q13_124
          · by_cases h125_130:V < 127
            · by_cases h125_127:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q13_125
              · have he:V = 126:=by omega
                subst V
                exact q13_126
            · by_cases h127_130:V < 128
              · have he:V = 127:=by omega
                subst V
                exact q13_127
              · by_cases h128_130:V < 129
                · have he:V = 128:=by omega
                  subst V
                  exact q13_128
                · have he:V = 129:=by omega
                  subst V
                  exact q13_129
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
