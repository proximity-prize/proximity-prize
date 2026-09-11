import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked04

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q5_0:ThresholdAt 5 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 0 0 (by decide +kernel)
  | exact S 5 0 1 (by decide +kernel)
  | exact S 5 0 2 (by decide +kernel)
  | exact S 5 0 3 (by decide +kernel)
  | exact S 5 0 4 (by decide +kernel)
  | exact S 5 0 5 (by decide +kernel)
theorem q5_1:ThresholdAt 5 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 1 0 (by decide +kernel)
  | exact S 5 1 1 (by decide +kernel)
  | exact S 5 1 2 (by decide +kernel)
  | exact S 5 1 3 (by decide +kernel)
  | exact S 5 1 4 (by decide +kernel)
  | exact S 5 1 5 (by decide +kernel)
theorem q5_2:ThresholdAt 5 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 2 0 (by decide +kernel)
  | exact S 5 2 1 (by decide +kernel)
  | exact S 5 2 2 (by decide +kernel)
  | exact S 5 2 3 (by decide +kernel)
  | exact S 5 2 4 (by decide +kernel)
  | exact S 5 2 5 (by decide +kernel)
theorem q5_3:ThresholdAt 5 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 3 0 (by decide +kernel)
  | exact S 5 3 1 (by decide +kernel)
  | exact S 5 3 2 (by decide +kernel)
  | exact S 5 3 3 (by decide +kernel)
  | exact S 5 3 4 (by decide +kernel)
  | exact S 5 3 5 (by decide +kernel)
theorem q5_4:ThresholdAt 5 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 4 0 (by decide +kernel)
  | exact S 5 4 1 (by decide +kernel)
  | exact S 5 4 2 (by decide +kernel)
  | exact S 5 4 3 (by decide +kernel)
  | exact S 5 4 4 (by decide +kernel)
  | exact S 5 4 5 (by decide +kernel)
theorem q5_5:ThresholdAt 5 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 5 0 (by decide +kernel)
  | exact S 5 5 1 (by decide +kernel)
  | exact S 5 5 2 (by decide +kernel)
  | exact S 5 5 3 (by decide +kernel)
  | exact S 5 5 4 (by decide +kernel)
  | exact S 5 5 5 (by decide +kernel)
theorem q5_6:ThresholdAt 5 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 6 0 (by decide +kernel)
  | exact S 5 6 1 (by decide +kernel)
  | exact S 5 6 2 (by decide +kernel)
  | exact S 5 6 3 (by decide +kernel)
  | exact S 5 6 4 (by decide +kernel)
  | exact S 5 6 5 (by decide +kernel)
theorem q5_7:ThresholdAt 5 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 7 0 (by decide +kernel)
  | exact S 5 7 1 (by decide +kernel)
  | exact S 5 7 2 (by decide +kernel)
  | exact S 5 7 3 (by decide +kernel)
  | exact S 5 7 4 (by decide +kernel)
  | exact S 5 7 5 (by decide +kernel)
theorem q5_8:ThresholdAt 5 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 8 0 (by decide +kernel)
  | exact S 5 8 1 (by decide +kernel)
  | exact S 5 8 2 (by decide +kernel)
  | exact S 5 8 3 (by decide +kernel)
  | exact S 5 8 4 (by decide +kernel)
  | exact S 5 8 5 (by decide +kernel)
theorem q5_9:ThresholdAt 5 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 9 0 (by decide +kernel)
  | exact S 5 9 1 (by decide +kernel)
  | exact S 5 9 2 (by decide +kernel)
  | exact S 5 9 3 (by decide +kernel)
  | exact S 5 9 4 (by decide +kernel)
  | exact S 5 9 5 (by decide +kernel)
theorem q5_10:ThresholdAt 5 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 10 0 (by decide +kernel)
  | exact S 5 10 1 (by decide +kernel)
  | exact S 5 10 2 (by decide +kernel)
  | exact S 5 10 3 (by decide +kernel)
  | exact S 5 10 4 (by decide +kernel)
  | exact S 5 10 5 (by decide +kernel)
theorem q5_11:ThresholdAt 5 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 11 0 (by decide +kernel)
  | exact S 5 11 1 (by decide +kernel)
  | exact S 5 11 2 (by decide +kernel)
  | exact S 5 11 3 (by decide +kernel)
  | exact S 5 11 4 (by decide +kernel)
  | exact S 5 11 5 (by decide +kernel)
theorem q5_12:ThresholdAt 5 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 12 0 (by decide +kernel)
  | exact S 5 12 1 (by decide +kernel)
  | exact S 5 12 2 (by decide +kernel)
  | exact S 5 12 3 (by decide +kernel)
  | exact S 5 12 4 (by decide +kernel)
  | exact S 5 12 5 (by decide +kernel)
theorem q5_13:ThresholdAt 5 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 13 0 (by decide +kernel)
  | exact S 5 13 1 (by decide +kernel)
  | exact S 5 13 2 (by decide +kernel)
  | exact S 5 13 3 (by decide +kernel)
  | exact S 5 13 4 (by decide +kernel)
  | exact S 5 13 5 (by decide +kernel)
theorem q5_14:ThresholdAt 5 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 14 0 (by decide +kernel)
  | exact S 5 14 1 (by decide +kernel)
  | exact S 5 14 2 (by decide +kernel)
  | exact S 5 14 3 (by decide +kernel)
  | exact S 5 14 4 (by decide +kernel)
  | exact S 5 14 5 (by decide +kernel)
theorem q5_15:ThresholdAt 5 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 15 0 (by decide +kernel)
  | exact S 5 15 1 (by decide +kernel)
  | exact S 5 15 2 (by decide +kernel)
  | exact S 5 15 3 (by decide +kernel)
  | exact S 5 15 4 (by decide +kernel)
  | exact S 5 15 5 (by decide +kernel)
theorem q5_16:ThresholdAt 5 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 16 0 (by decide +kernel)
  | exact S 5 16 1 (by decide +kernel)
  | exact S 5 16 2 (by decide +kernel)
  | exact S 5 16 3 (by decide +kernel)
  | exact S 5 16 4 (by decide +kernel)
  | exact S 5 16 5 (by decide +kernel)
theorem q5_17:ThresholdAt 5 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 17 0 (by decide +kernel)
  | exact S 5 17 1 (by decide +kernel)
  | exact S 5 17 2 (by decide +kernel)
  | exact S 5 17 3 (by decide +kernel)
  | exact S 5 17 4 (by decide +kernel)
  | exact S 5 17 5 (by decide +kernel)
theorem q5_18:ThresholdAt 5 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 18 0 (by decide +kernel)
  | exact S 5 18 1 (by decide +kernel)
  | exact S 5 18 2 (by decide +kernel)
  | exact S 5 18 3 (by decide +kernel)
  | exact S 5 18 4 (by decide +kernel)
  | exact S 5 18 5 (by decide +kernel)
theorem q5_19:ThresholdAt 5 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 19 0 (by decide +kernel)
  | exact S 5 19 1 (by decide +kernel)
  | exact S 5 19 2 (by decide +kernel)
  | exact S 5 19 3 (by decide +kernel)
  | exact S 5 19 4 (by decide +kernel)
  | exact S 5 19 5 (by decide +kernel)
theorem q5_20:ThresholdAt 5 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 20 0 (by decide +kernel)
  | exact S 5 20 1 (by decide +kernel)
  | exact S 5 20 2 (by decide +kernel)
  | exact S 5 20 3 (by decide +kernel)
  | exact S 5 20 4 (by decide +kernel)
  | exact S 5 20 5 (by decide +kernel)
theorem q5_21:ThresholdAt 5 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 21 0 (by decide +kernel)
  | exact S 5 21 1 (by decide +kernel)
  | exact S 5 21 2 (by decide +kernel)
  | exact S 5 21 3 (by decide +kernel)
  | exact S 5 21 4 (by decide +kernel)
  | exact S 5 21 5 (by decide +kernel)
theorem q5_22:ThresholdAt 5 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 22 0 (by decide +kernel)
  | exact S 5 22 1 (by decide +kernel)
  | exact S 5 22 2 (by decide +kernel)
  | exact S 5 22 3 (by decide +kernel)
  | exact S 5 22 4 (by decide +kernel)
  | exact S 5 22 5 (by decide +kernel)
theorem q5_23:ThresholdAt 5 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 23 0 (by decide +kernel)
  | exact S 5 23 1 (by decide +kernel)
  | exact S 5 23 2 (by decide +kernel)
  | exact S 5 23 3 (by decide +kernel)
  | exact S 5 23 4 (by decide +kernel)
  | exact S 5 23 5 (by decide +kernel)
theorem q5_24:ThresholdAt 5 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 24 0 (by decide +kernel)
  | exact S 5 24 1 (by decide +kernel)
  | exact S 5 24 2 (by decide +kernel)
  | exact S 5 24 3 (by decide +kernel)
  | exact S 5 24 4 (by decide +kernel)
  | exact S 5 24 5 (by decide +kernel)
theorem q5_25:ThresholdAt 5 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 25 0 (by decide +kernel)
  | exact S 5 25 1 (by decide +kernel)
  | exact S 5 25 2 (by decide +kernel)
  | exact S 5 25 3 (by decide +kernel)
  | exact S 5 25 4 (by decide +kernel)
  | exact S 5 25 5 (by decide +kernel)
theorem q5_26:ThresholdAt 5 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 26 0 (by decide +kernel)
  | exact S 5 26 1 (by decide +kernel)
  | exact S 5 26 2 (by decide +kernel)
  | exact S 5 26 3 (by decide +kernel)
  | exact S 5 26 4 (by decide +kernel)
  | exact S 5 26 5 (by decide +kernel)
theorem q5_27:ThresholdAt 5 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 27 0 (by decide +kernel)
  | exact S 5 27 1 (by decide +kernel)
  | exact S 5 27 2 (by decide +kernel)
  | exact S 5 27 3 (by decide +kernel)
  | exact S 5 27 4 (by decide +kernel)
  | exact S 5 27 5 (by decide +kernel)
theorem q5_28:ThresholdAt 5 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 28 0 (by decide +kernel)
  | exact S 5 28 1 (by decide +kernel)
  | exact S 5 28 2 (by decide +kernel)
  | exact S 5 28 3 (by decide +kernel)
  | exact S 5 28 4 (by decide +kernel)
  | exact S 5 28 5 (by decide +kernel)
theorem q5_29:ThresholdAt 5 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 29 0 (by decide +kernel)
  | exact S 5 29 1 (by decide +kernel)
  | exact S 5 29 2 (by decide +kernel)
  | exact S 5 29 3 (by decide +kernel)
  | exact S 5 29 4 (by decide +kernel)
  | exact S 5 29 5 (by decide +kernel)
theorem q5_30:ThresholdAt 5 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 30 0 (by decide +kernel)
  | exact S 5 30 1 (by decide +kernel)
  | exact S 5 30 2 (by decide +kernel)
  | exact S 5 30 3 (by decide +kernel)
  | exact S 5 30 4 (by decide +kernel)
  | exact S 5 30 5 (by decide +kernel)
theorem q5_31:ThresholdAt 5 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 31 0 (by decide +kernel)
  | exact S 5 31 1 (by decide +kernel)
  | exact S 5 31 2 (by decide +kernel)
  | exact S 5 31 3 (by decide +kernel)
  | exact S 5 31 4 (by decide +kernel)
  | exact S 5 31 5 (by decide +kernel)
theorem q5_32:ThresholdAt 5 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 32 0 (by decide +kernel)
  | exact S 5 32 1 (by decide +kernel)
  | exact S 5 32 2 (by decide +kernel)
  | exact S 5 32 3 (by decide +kernel)
  | exact S 5 32 4 (by decide +kernel)
  | exact S 5 32 5 (by decide +kernel)
theorem q5_33:ThresholdAt 5 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 33 0 (by decide +kernel)
  | exact S 5 33 1 (by decide +kernel)
  | exact S 5 33 2 (by decide +kernel)
  | exact S 5 33 3 (by decide +kernel)
  | exact S 5 33 4 (by decide +kernel)
  | exact S 5 33 5 (by decide +kernel)
theorem q5_34:ThresholdAt 5 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 34 0 (by decide +kernel)
  | exact S 5 34 1 (by decide +kernel)
  | exact S 5 34 2 (by decide +kernel)
  | exact S 5 34 3 (by decide +kernel)
  | exact S 5 34 4 (by decide +kernel)
  | exact S 5 34 5 (by decide +kernel)
theorem q5_35:ThresholdAt 5 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 35 0 (by decide +kernel)
  | exact S 5 35 1 (by decide +kernel)
  | exact S 5 35 2 (by decide +kernel)
  | exact S 5 35 3 (by decide +kernel)
  | exact S 5 35 4 (by decide +kernel)
  | exact S 5 35 5 (by decide +kernel)
theorem q5_36:ThresholdAt 5 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 36 0 (by decide +kernel)
  | exact S 5 36 1 (by decide +kernel)
  | exact S 5 36 2 (by decide +kernel)
  | exact S 5 36 3 (by decide +kernel)
  | exact S 5 36 4 (by decide +kernel)
  | exact S 5 36 5 (by decide +kernel)
theorem q5_37:ThresholdAt 5 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 37 0 (by decide +kernel)
  | exact S 5 37 1 (by decide +kernel)
  | exact S 5 37 2 (by decide +kernel)
  | exact S 5 37 3 (by decide +kernel)
  | exact S 5 37 4 (by decide +kernel)
  | exact S 5 37 5 (by decide +kernel)
theorem q5_38:ThresholdAt 5 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 38 0 (by decide +kernel)
  | exact S 5 38 1 (by decide +kernel)
  | exact S 5 38 2 (by decide +kernel)
  | exact S 5 38 3 (by decide +kernel)
  | exact S 5 38 4 (by decide +kernel)
  | exact S 5 38 5 (by decide +kernel)
theorem q5_39:ThresholdAt 5 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 39 0 (by decide +kernel)
  | exact S 5 39 1 (by decide +kernel)
  | exact S 5 39 2 (by decide +kernel)
  | exact S 5 39 3 (by decide +kernel)
  | exact S 5 39 4 (by decide +kernel)
  | exact S 5 39 5 (by decide +kernel)
theorem q5_40:ThresholdAt 5 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 40 0 (by decide +kernel)
  | exact S 5 40 1 (by decide +kernel)
  | exact S 5 40 2 (by decide +kernel)
  | exact S 5 40 3 (by decide +kernel)
  | exact S 5 40 4 (by decide +kernel)
  | exact S 5 40 5 (by decide +kernel)
theorem q5_41:ThresholdAt 5 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 41 0 (by decide +kernel)
  | exact S 5 41 1 (by decide +kernel)
  | exact S 5 41 2 (by decide +kernel)
  | exact S 5 41 3 (by decide +kernel)
  | exact S 5 41 4 (by decide +kernel)
  | exact S 5 41 5 (by decide +kernel)
theorem q5_42:ThresholdAt 5 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 42 0 (by decide +kernel)
  | exact S 5 42 1 (by decide +kernel)
  | exact S 5 42 2 (by decide +kernel)
  | exact S 5 42 3 (by decide +kernel)
  | exact S 5 42 4 (by decide +kernel)
  | exact S 5 42 5 (by decide +kernel)
theorem q5_43:ThresholdAt 5 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 43 0 (by decide +kernel)
  | exact S 5 43 1 (by decide +kernel)
  | exact S 5 43 2 (by decide +kernel)
  | exact S 5 43 3 (by decide +kernel)
  | exact S 5 43 4 (by decide +kernel)
  | exact S 5 43 5 (by decide +kernel)
theorem q5_44:ThresholdAt 5 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 44 0 (by decide +kernel)
  | exact S 5 44 1 (by decide +kernel)
  | exact S 5 44 2 (by decide +kernel)
  | exact S 5 44 3 (by decide +kernel)
  | exact S 5 44 4 (by decide +kernel)
  | exact S 5 44 5 (by decide +kernel)
theorem q5_45:ThresholdAt 5 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 45 0 (by decide +kernel)
  | exact S 5 45 1 (by decide +kernel)
  | exact S 5 45 2 (by decide +kernel)
  | exact S 5 45 3 (by decide +kernel)
  | exact S 5 45 4 (by decide +kernel)
  | exact S 5 45 5 (by decide +kernel)
theorem q5_46:ThresholdAt 5 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 46 0 (by decide +kernel)
  | exact S 5 46 1 (by decide +kernel)
  | exact S 5 46 2 (by decide +kernel)
  | exact S 5 46 3 (by decide +kernel)
  | exact S 5 46 4 (by decide +kernel)
  | exact S 5 46 5 (by decide +kernel)
theorem q5_47:ThresholdAt 5 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 47 0 (by decide +kernel)
  | exact S 5 47 1 (by decide +kernel)
  | exact S 5 47 2 (by decide +kernel)
  | exact S 5 47 3 (by decide +kernel)
  | exact S 5 47 4 (by decide +kernel)
  | exact S 5 47 5 (by decide +kernel)
theorem q5_48:ThresholdAt 5 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 48 0 (by decide +kernel)
  | exact S 5 48 1 (by decide +kernel)
  | exact S 5 48 2 (by decide +kernel)
  | exact S 5 48 3 (by decide +kernel)
  | exact S 5 48 4 (by decide +kernel)
  | exact S 5 48 5 (by decide +kernel)
theorem q5_49:ThresholdAt 5 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 49 0 (by decide +kernel)
  | exact S 5 49 1 (by decide +kernel)
  | exact S 5 49 2 (by decide +kernel)
  | exact S 5 49 3 (by decide +kernel)
  | exact S 5 49 4 (by decide +kernel)
  | exact S 5 49 5 (by decide +kernel)
theorem q5_50:ThresholdAt 5 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 50 0 (by decide +kernel)
  | exact S 5 50 1 (by decide +kernel)
  | exact S 5 50 2 (by decide +kernel)
  | exact S 5 50 3 (by decide +kernel)
  | exact S 5 50 4 (by decide +kernel)
  | exact S 5 50 5 (by decide +kernel)
theorem q5_51:ThresholdAt 5 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 51 0 (by decide +kernel)
  | exact S 5 51 1 (by decide +kernel)
  | exact S 5 51 2 (by decide +kernel)
  | exact S 5 51 3 (by decide +kernel)
  | exact S 5 51 4 (by decide +kernel)
  | exact S 5 51 5 (by decide +kernel)
theorem q5_52:ThresholdAt 5 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 52 0 (by decide +kernel)
  | exact S 5 52 1 (by decide +kernel)
  | exact S 5 52 2 (by decide +kernel)
  | exact S 5 52 3 (by decide +kernel)
  | exact S 5 52 4 (by decide +kernel)
  | exact S 5 52 5 (by decide +kernel)
theorem q5_53:ThresholdAt 5 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 53 0 (by decide +kernel)
  | exact S 5 53 1 (by decide +kernel)
  | exact S 5 53 2 (by decide +kernel)
  | exact S 5 53 3 (by decide +kernel)
  | exact S 5 53 4 (by decide +kernel)
  | exact S 5 53 5 (by decide +kernel)
theorem q5_54:ThresholdAt 5 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 54 0 (by decide +kernel)
  | exact S 5 54 1 (by decide +kernel)
  | exact S 5 54 2 (by decide +kernel)
  | exact S 5 54 3 (by decide +kernel)
  | exact S 5 54 4 (by decide +kernel)
  | exact S 5 54 5 (by decide +kernel)
theorem q5_55:ThresholdAt 5 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 55 0 (by decide +kernel)
  | exact S 5 55 1 (by decide +kernel)
  | exact S 5 55 2 (by decide +kernel)
  | exact S 5 55 3 (by decide +kernel)
  | exact S 5 55 4 (by decide +kernel)
  | exact S 5 55 5 (by decide +kernel)
theorem q5_56:ThresholdAt 5 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 56 0 (by decide +kernel)
  | exact S 5 56 1 (by decide +kernel)
  | exact S 5 56 2 (by decide +kernel)
  | exact S 5 56 3 (by decide +kernel)
  | exact S 5 56 4 (by decide +kernel)
  | exact S 5 56 5 (by decide +kernel)
theorem q5_57:ThresholdAt 5 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 57 0 (by decide +kernel)
  | exact S 5 57 1 (by decide +kernel)
  | exact S 5 57 2 (by decide +kernel)
  | exact S 5 57 3 (by decide +kernel)
  | exact S 5 57 4 (by decide +kernel)
  | exact S 5 57 5 (by decide +kernel)
theorem q5_58:ThresholdAt 5 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 58 0 (by decide +kernel)
  | exact S 5 58 1 (by decide +kernel)
  | exact S 5 58 2 (by decide +kernel)
  | exact S 5 58 3 (by decide +kernel)
  | exact S 5 58 4 (by decide +kernel)
  | exact S 5 58 5 (by decide +kernel)
theorem q5_59:ThresholdAt 5 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 59 0 (by decide +kernel)
  | exact S 5 59 1 (by decide +kernel)
  | exact S 5 59 2 (by decide +kernel)
  | exact S 5 59 3 (by decide +kernel)
  | exact S 5 59 4 (by decide +kernel)
  | exact S 5 59 5 (by decide +kernel)
theorem q5_60:ThresholdAt 5 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 60 0 (by decide +kernel)
  | exact S 5 60 1 (by decide +kernel)
  | exact S 5 60 2 (by decide +kernel)
  | exact S 5 60 3 (by decide +kernel)
  | exact S 5 60 4 (by decide +kernel)
  | exact S 5 60 5 (by decide +kernel)
theorem q5_61:ThresholdAt 5 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 61 0 (by decide +kernel)
  | exact S 5 61 1 (by decide +kernel)
  | exact S 5 61 2 (by decide +kernel)
  | exact S 5 61 3 (by decide +kernel)
  | exact S 5 61 4 (by decide +kernel)
  | exact S 5 61 5 (by decide +kernel)
theorem q5_62:ThresholdAt 5 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 62 0 (by decide +kernel)
  | exact S 5 62 1 (by decide +kernel)
  | exact S 5 62 2 (by decide +kernel)
  | exact S 5 62 3 (by decide +kernel)
  | exact S 5 62 4 (by decide +kernel)
  | exact S 5 62 5 (by decide +kernel)
theorem q5_63:ThresholdAt 5 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 63 0 (by decide +kernel)
  | exact S 5 63 1 (by decide +kernel)
  | exact S 5 63 2 (by decide +kernel)
  | exact S 5 63 3 (by decide +kernel)
  | exact S 5 63 4 (by decide +kernel)
  | exact S 5 63 5 (by decide +kernel)
theorem q5_64:ThresholdAt 5 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 64 0 (by decide +kernel)
  | exact S 5 64 1 (by decide +kernel)
  | exact S 5 64 2 (by decide +kernel)
  | exact S 5 64 3 (by decide +kernel)
  | exact S 5 64 4 (by decide +kernel)
  | exact S 5 64 5 (by decide +kernel)
theorem q5_65:ThresholdAt 5 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 65 0 (by decide +kernel)
  | exact S 5 65 1 (by decide +kernel)
  | exact S 5 65 2 (by decide +kernel)
  | exact S 5 65 3 (by decide +kernel)
  | exact S 5 65 4 (by decide +kernel)
  | exact S 5 65 5 (by decide +kernel)
theorem q5_66:ThresholdAt 5 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 66 0 (by decide +kernel)
  | exact S 5 66 1 (by decide +kernel)
  | exact S 5 66 2 (by decide +kernel)
  | exact S 5 66 3 (by decide +kernel)
  | exact S 5 66 4 (by decide +kernel)
  | exact S 5 66 5 (by decide +kernel)
theorem q5_67:ThresholdAt 5 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 67 0 (by decide +kernel)
  | exact S 5 67 1 (by decide +kernel)
  | exact S 5 67 2 (by decide +kernel)
  | exact S 5 67 3 (by decide +kernel)
  | exact S 5 67 4 (by decide +kernel)
  | exact S 5 67 5 (by decide +kernel)
theorem q5_68:ThresholdAt 5 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 68 0 (by decide +kernel)
  | exact S 5 68 1 (by decide +kernel)
  | exact S 5 68 2 (by decide +kernel)
  | exact S 5 68 3 (by decide +kernel)
  | exact S 5 68 4 (by decide +kernel)
  | exact S 5 68 5 (by decide +kernel)
theorem q5_69:ThresholdAt 5 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 69 0 (by decide +kernel)
  | exact S 5 69 1 (by decide +kernel)
  | exact S 5 69 2 (by decide +kernel)
  | exact S 5 69 3 (by decide +kernel)
  | exact S 5 69 4 (by decide +kernel)
  | exact S 5 69 5 (by decide +kernel)
theorem q5_70:ThresholdAt 5 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 70 0 (by decide +kernel)
  | exact S 5 70 1 (by decide +kernel)
  | exact S 5 70 2 (by decide +kernel)
  | exact S 5 70 3 (by decide +kernel)
  | exact S 5 70 4 (by decide +kernel)
  | exact S 5 70 5 (by decide +kernel)
theorem q5_71:ThresholdAt 5 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 71 0 (by decide +kernel)
  | exact S 5 71 1 (by decide +kernel)
  | exact S 5 71 2 (by decide +kernel)
  | exact S 5 71 3 (by decide +kernel)
  | exact S 5 71 4 (by decide +kernel)
  | exact S 5 71 5 (by decide +kernel)
theorem q5_72:ThresholdAt 5 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 72 0 (by decide +kernel)
  | exact S 5 72 1 (by decide +kernel)
  | exact S 5 72 2 (by decide +kernel)
  | exact S 5 72 3 (by decide +kernel)
  | exact S 5 72 4 (by decide +kernel)
  | exact S 5 72 5 (by decide +kernel)
theorem q5_73:ThresholdAt 5 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 73 0 (by decide +kernel)
  | exact S 5 73 1 (by decide +kernel)
  | exact S 5 73 2 (by decide +kernel)
  | exact S 5 73 3 (by decide +kernel)
  | exact S 5 73 4 (by decide +kernel)
  | exact S 5 73 5 (by decide +kernel)
theorem q5_74:ThresholdAt 5 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 74 0 (by decide +kernel)
  | exact S 5 74 1 (by decide +kernel)
  | exact S 5 74 2 (by decide +kernel)
  | exact S 5 74 3 (by decide +kernel)
  | exact S 5 74 4 (by decide +kernel)
  | exact S 5 74 5 (by decide +kernel)
theorem q5_75:ThresholdAt 5 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 75 0 (by decide +kernel)
  | exact S 5 75 1 (by decide +kernel)
  | exact S 5 75 2 (by decide +kernel)
  | exact S 5 75 3 (by decide +kernel)
  | exact S 5 75 4 (by decide +kernel)
  | exact S 5 75 5 (by decide +kernel)
theorem q5_76:ThresholdAt 5 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 76 0 (by decide +kernel)
  | exact S 5 76 1 (by decide +kernel)
  | exact S 5 76 2 (by decide +kernel)
  | exact S 5 76 3 (by decide +kernel)
  | exact S 5 76 4 (by decide +kernel)
  | exact S 5 76 5 (by decide +kernel)
theorem q5_77:ThresholdAt 5 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 77 0 (by decide +kernel)
  | exact S 5 77 1 (by decide +kernel)
  | exact S 5 77 2 (by decide +kernel)
  | exact S 5 77 3 (by decide +kernel)
  | exact S 5 77 4 (by decide +kernel)
  | exact S 5 77 5 (by decide +kernel)
theorem q5_78:ThresholdAt 5 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 78 0 (by decide +kernel)
  | exact S 5 78 1 (by decide +kernel)
  | exact S 5 78 2 (by decide +kernel)
  | exact S 5 78 3 (by decide +kernel)
  | exact S 5 78 4 (by decide +kernel)
  | exact S 5 78 5 (by decide +kernel)
theorem q5_79:ThresholdAt 5 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 79 0 (by decide +kernel)
  | exact S 5 79 1 (by decide +kernel)
  | exact S 5 79 2 (by decide +kernel)
  | exact S 5 79 3 (by decide +kernel)
  | exact S 5 79 4 (by decide +kernel)
  | exact S 5 79 5 (by decide +kernel)
theorem q5_80:ThresholdAt 5 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 80 0 (by decide +kernel)
  | exact S 5 80 1 (by decide +kernel)
  | exact S 5 80 2 (by decide +kernel)
  | exact S 5 80 3 (by decide +kernel)
  | exact S 5 80 4 (by decide +kernel)
  | exact S 5 80 5 (by decide +kernel)
theorem q5_81:ThresholdAt 5 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 81 0 (by decide +kernel)
  | exact S 5 81 1 (by decide +kernel)
  | exact S 5 81 2 (by decide +kernel)
  | exact S 5 81 3 (by decide +kernel)
  | exact S 5 81 4 (by decide +kernel)
  | exact S 5 81 5 (by decide +kernel)
theorem q5_82:ThresholdAt 5 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 82 0 (by decide +kernel)
  | exact S 5 82 1 (by decide +kernel)
  | exact S 5 82 2 (by decide +kernel)
  | exact S 5 82 3 (by decide +kernel)
  | exact S 5 82 4 (by decide +kernel)
  | exact S 5 82 5 (by decide +kernel)
theorem q5_83:ThresholdAt 5 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 83 0 (by decide +kernel)
  | exact S 5 83 1 (by decide +kernel)
  | exact S 5 83 2 (by decide +kernel)
  | exact S 5 83 3 (by decide +kernel)
  | exact S 5 83 4 (by decide +kernel)
  | exact S 5 83 5 (by decide +kernel)
theorem q5_84:ThresholdAt 5 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 84 0 (by decide +kernel)
  | exact S 5 84 1 (by decide +kernel)
  | exact S 5 84 2 (by decide +kernel)
  | exact S 5 84 3 (by decide +kernel)
  | exact S 5 84 4 (by decide +kernel)
  | exact S 5 84 5 (by decide +kernel)
theorem q5_85:ThresholdAt 5 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 85 0 (by decide +kernel)
  | exact S 5 85 1 (by decide +kernel)
  | exact S 5 85 2 (by decide +kernel)
  | exact S 5 85 3 (by decide +kernel)
  | exact S 5 85 4 (by decide +kernel)
  | exact S 5 85 5 (by decide +kernel)
theorem q5_86:ThresholdAt 5 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 86 0 (by decide +kernel)
  | exact S 5 86 1 (by decide +kernel)
  | exact S 5 86 2 (by decide +kernel)
  | exact S 5 86 3 (by decide +kernel)
  | exact S 5 86 4 (by decide +kernel)
  | exact S 5 86 5 (by decide +kernel)
theorem q5_87:ThresholdAt 5 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 87 0 (by decide +kernel)
  | exact S 5 87 1 (by decide +kernel)
  | exact S 5 87 2 (by decide +kernel)
  | exact S 5 87 3 (by decide +kernel)
  | exact S 5 87 4 (by decide +kernel)
  | exact S 5 87 5 (by decide +kernel)
theorem q5_88:ThresholdAt 5 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 88 0 (by decide +kernel)
  | exact S 5 88 1 (by decide +kernel)
  | exact S 5 88 2 (by decide +kernel)
  | exact S 5 88 3 (by decide +kernel)
  | exact S 5 88 4 (by decide +kernel)
  | exact S 5 88 5 (by decide +kernel)
theorem q5_89:ThresholdAt 5 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 89 0 (by decide +kernel)
  | exact S 5 89 1 (by decide +kernel)
  | exact S 5 89 2 (by decide +kernel)
  | exact S 5 89 3 (by decide +kernel)
  | exact S 5 89 4 (by decide +kernel)
  | exact S 5 89 5 (by decide +kernel)
theorem q5_90:ThresholdAt 5 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 90 0 (by decide +kernel)
  | exact S 5 90 1 (by decide +kernel)
  | exact S 5 90 2 (by decide +kernel)
  | exact S 5 90 3 (by decide +kernel)
  | exact S 5 90 4 (by decide +kernel)
  | exact S 5 90 5 (by decide +kernel)
theorem q5_91:ThresholdAt 5 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 91 0 (by decide +kernel)
  | exact S 5 91 1 (by decide +kernel)
  | exact S 5 91 2 (by decide +kernel)
  | exact S 5 91 3 (by decide +kernel)
  | exact S 5 91 4 (by decide +kernel)
  | exact S 5 91 5 (by decide +kernel)
theorem q5_92:ThresholdAt 5 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 92 0 (by decide +kernel)
  | exact S 5 92 1 (by decide +kernel)
  | exact S 5 92 2 (by decide +kernel)
  | exact S 5 92 3 (by decide +kernel)
  | exact S 5 92 4 (by decide +kernel)
  | exact S 5 92 5 (by decide +kernel)
theorem q5_93:ThresholdAt 5 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 93 0 (by decide +kernel)
  | exact S 5 93 1 (by decide +kernel)
  | exact S 5 93 2 (by decide +kernel)
  | exact S 5 93 3 (by decide +kernel)
  | exact S 5 93 4 (by decide +kernel)
  | exact S 5 93 5 (by decide +kernel)
theorem q5_94:ThresholdAt 5 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 94 0 (by decide +kernel)
  | exact S 5 94 1 (by decide +kernel)
  | exact S 5 94 2 (by decide +kernel)
  | exact S 5 94 3 (by decide +kernel)
  | exact S 5 94 4 (by decide +kernel)
  | exact S 5 94 5 (by decide +kernel)
theorem q5_95:ThresholdAt 5 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 95 0 (by decide +kernel)
  | exact S 5 95 1 (by decide +kernel)
  | exact S 5 95 2 (by decide +kernel)
  | exact S 5 95 3 (by decide +kernel)
  | exact S 5 95 4 (by decide +kernel)
  | exact S 5 95 5 (by decide +kernel)
theorem q5_96:ThresholdAt 5 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 96 0 (by decide +kernel)
  | exact S 5 96 1 (by decide +kernel)
  | exact S 5 96 2 (by decide +kernel)
  | exact S 5 96 3 (by decide +kernel)
  | exact S 5 96 4 (by decide +kernel)
  | exact S 5 96 5 (by decide +kernel)
theorem q5_97:ThresholdAt 5 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 97 0 (by decide +kernel)
  | exact S 5 97 1 (by decide +kernel)
  | exact S 5 97 2 (by decide +kernel)
  | exact S 5 97 3 (by decide +kernel)
  | exact S 5 97 4 (by decide +kernel)
  | exact S 5 97 5 (by decide +kernel)
theorem q5_98:ThresholdAt 5 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 98 0 (by decide +kernel)
  | exact S 5 98 1 (by decide +kernel)
  | exact S 5 98 2 (by decide +kernel)
  | exact S 5 98 3 (by decide +kernel)
  | exact S 5 98 4 (by decide +kernel)
  | exact S 5 98 5 (by decide +kernel)
theorem q5_99:ThresholdAt 5 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 99 0 (by decide +kernel)
  | exact S 5 99 1 (by decide +kernel)
  | exact S 5 99 2 (by decide +kernel)
  | exact S 5 99 3 (by decide +kernel)
  | exact S 5 99 4 (by decide +kernel)
  | exact S 5 99 5 (by decide +kernel)
theorem q5_100:ThresholdAt 5 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 100 0 (by decide +kernel)
  | exact S 5 100 1 (by decide +kernel)
  | exact S 5 100 2 (by decide +kernel)
  | exact S 5 100 3 (by decide +kernel)
  | exact S 5 100 4 (by decide +kernel)
  | exact S 5 100 5 (by decide +kernel)
theorem q5_101:ThresholdAt 5 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 101 0 (by decide +kernel)
  | exact S 5 101 1 (by decide +kernel)
  | exact S 5 101 2 (by decide +kernel)
  | exact S 5 101 3 (by decide +kernel)
  | exact S 5 101 4 (by decide +kernel)
  | exact S 5 101 5 (by decide +kernel)
theorem q5_102:ThresholdAt 5 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 102 0 (by decide +kernel)
  | exact S 5 102 1 (by decide +kernel)
  | exact S 5 102 2 (by decide +kernel)
  | exact S 5 102 3 (by decide +kernel)
  | exact S 5 102 4 (by decide +kernel)
  | exact S 5 102 5 (by decide +kernel)
theorem q5_103:ThresholdAt 5 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 103 0 (by decide +kernel)
  | exact S 5 103 1 (by decide +kernel)
  | exact S 5 103 2 (by decide +kernel)
  | exact S 5 103 3 (by decide +kernel)
  | exact S 5 103 4 (by decide +kernel)
  | exact S 5 103 5 (by decide +kernel)
theorem q5_104:ThresholdAt 5 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 104 0 (by decide +kernel)
  | exact S 5 104 1 (by decide +kernel)
  | exact S 5 104 2 (by decide +kernel)
  | exact S 5 104 3 (by decide +kernel)
  | exact S 5 104 4 (by decide +kernel)
  | exact S 5 104 5 (by decide +kernel)
theorem q5_105:ThresholdAt 5 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 105 0 (by decide +kernel)
  | exact S 5 105 1 (by decide +kernel)
  | exact S 5 105 2 (by decide +kernel)
  | exact S 5 105 3 (by decide +kernel)
  | exact S 5 105 4 (by decide +kernel)
  | exact S 5 105 5 (by decide +kernel)
theorem q5_106:ThresholdAt 5 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 106 0 (by decide +kernel)
  | exact S 5 106 1 (by decide +kernel)
  | exact S 5 106 2 (by decide +kernel)
  | exact S 5 106 3 (by decide +kernel)
  | exact S 5 106 4 (by decide +kernel)
  | exact S 5 106 5 (by decide +kernel)
theorem q5_107:ThresholdAt 5 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 107 0 (by decide +kernel)
  | exact S 5 107 1 (by decide +kernel)
  | exact S 5 107 2 (by decide +kernel)
  | exact S 5 107 3 (by decide +kernel)
  | exact S 5 107 4 (by decide +kernel)
  | exact S 5 107 5 (by decide +kernel)
theorem q5_108:ThresholdAt 5 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 108 0 (by decide +kernel)
  | exact S 5 108 1 (by decide +kernel)
  | exact S 5 108 2 (by decide +kernel)
  | exact S 5 108 3 (by decide +kernel)
  | exact S 5 108 4 (by decide +kernel)
  | exact S 5 108 5 (by decide +kernel)
theorem q5_109:ThresholdAt 5 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 109 0 (by decide +kernel)
  | exact S 5 109 1 (by decide +kernel)
  | exact S 5 109 2 (by decide +kernel)
  | exact S 5 109 3 (by decide +kernel)
  | exact S 5 109 4 (by decide +kernel)
  | exact S 5 109 5 (by decide +kernel)
theorem q5_110:ThresholdAt 5 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 110 0 (by decide +kernel)
  | exact S 5 110 1 (by decide +kernel)
  | exact S 5 110 2 (by decide +kernel)
  | exact S 5 110 3 (by decide +kernel)
  | exact S 5 110 4 (by decide +kernel)
  | exact S 5 110 5 (by decide +kernel)
theorem q5_111:ThresholdAt 5 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 111 0 (by decide +kernel)
  | exact S 5 111 1 (by decide +kernel)
  | exact S 5 111 2 (by decide +kernel)
  | exact S 5 111 3 (by decide +kernel)
  | exact S 5 111 4 (by decide +kernel)
  | exact S 5 111 5 (by decide +kernel)
theorem q5_112:ThresholdAt 5 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 112 0 (by decide +kernel)
  | exact S 5 112 1 (by decide +kernel)
  | exact S 5 112 2 (by decide +kernel)
  | exact S 5 112 3 (by decide +kernel)
  | exact S 5 112 4 (by decide +kernel)
  | exact S 5 112 5 (by decide +kernel)
theorem q5_113:ThresholdAt 5 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 113 0 (by decide +kernel)
  | exact S 5 113 1 (by decide +kernel)
  | exact S 5 113 2 (by decide +kernel)
  | exact S 5 113 3 (by decide +kernel)
  | exact S 5 113 4 (by decide +kernel)
  | exact S 5 113 5 (by decide +kernel)
theorem q5_114:ThresholdAt 5 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 114 0 (by decide +kernel)
  | exact S 5 114 1 (by decide +kernel)
  | exact S 5 114 2 (by decide +kernel)
  | exact S 5 114 3 (by decide +kernel)
  | exact S 5 114 4 (by decide +kernel)
  | exact S 5 114 5 (by decide +kernel)
theorem q5_115:ThresholdAt 5 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 115 0 (by decide +kernel)
  | exact S 5 115 1 (by decide +kernel)
  | exact S 5 115 2 (by decide +kernel)
  | exact S 5 115 3 (by decide +kernel)
  | exact S 5 115 4 (by decide +kernel)
  | exact S 5 115 5 (by decide +kernel)
theorem q5_116:ThresholdAt 5 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 116 0 (by decide +kernel)
  | exact S 5 116 1 (by decide +kernel)
  | exact S 5 116 2 (by decide +kernel)
  | exact S 5 116 3 (by decide +kernel)
  | exact S 5 116 4 (by decide +kernel)
  | exact S 5 116 5 (by decide +kernel)
theorem q5_117:ThresholdAt 5 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 117 0 (by decide +kernel)
  | exact S 5 117 1 (by decide +kernel)
  | exact S 5 117 2 (by decide +kernel)
  | exact S 5 117 3 (by decide +kernel)
  | exact S 5 117 4 (by decide +kernel)
  | exact S 5 117 5 (by decide +kernel)
theorem q5_118:ThresholdAt 5 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 118 0 (by decide +kernel)
  | exact S 5 118 1 (by decide +kernel)
  | exact S 5 118 2 (by decide +kernel)
  | exact S 5 118 3 (by decide +kernel)
  | exact S 5 118 4 (by decide +kernel)
  | exact S 5 118 5 (by decide +kernel)
theorem q5_119:ThresholdAt 5 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 119 0 (by decide +kernel)
  | exact S 5 119 1 (by decide +kernel)
  | exact S 5 119 2 (by decide +kernel)
  | exact S 5 119 3 (by decide +kernel)
  | exact S 5 119 4 (by decide +kernel)
  | exact S 5 119 5 (by decide +kernel)
theorem q5_120:ThresholdAt 5 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 120 0 (by decide +kernel)
  | exact S 5 120 1 (by decide +kernel)
  | exact S 5 120 2 (by decide +kernel)
  | exact S 5 120 3 (by decide +kernel)
  | exact S 5 120 4 (by decide +kernel)
  | exact S 5 120 5 (by decide +kernel)
theorem q5_121:ThresholdAt 5 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 121 0 (by decide +kernel)
  | exact S 5 121 1 (by decide +kernel)
  | exact S 5 121 2 (by decide +kernel)
  | exact S 5 121 3 (by decide +kernel)
  | exact S 5 121 4 (by decide +kernel)
  | exact S 5 121 5 (by decide +kernel)
theorem q5_122:ThresholdAt 5 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 122 0 (by decide +kernel)
  | exact S 5 122 1 (by decide +kernel)
  | exact S 5 122 2 (by decide +kernel)
  | exact S 5 122 3 (by decide +kernel)
  | exact S 5 122 4 (by decide +kernel)
  | exact S 5 122 5 (by decide +kernel)
theorem q5_123:ThresholdAt 5 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 123 0 (by decide +kernel)
  | exact S 5 123 1 (by decide +kernel)
  | exact S 5 123 2 (by decide +kernel)
  | exact S 5 123 3 (by decide +kernel)
  | exact S 5 123 4 (by decide +kernel)
  | exact S 5 123 5 (by decide +kernel)
theorem q5_124:ThresholdAt 5 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 124 0 (by decide +kernel)
  | exact S 5 124 1 (by decide +kernel)
  | exact S 5 124 2 (by decide +kernel)
  | exact S 5 124 3 (by decide +kernel)
  | exact S 5 124 4 (by decide +kernel)
  | exact S 5 124 5 (by decide +kernel)
theorem q5_125:ThresholdAt 5 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 125 0 (by decide +kernel)
  | exact S 5 125 1 (by decide +kernel)
  | exact S 5 125 2 (by decide +kernel)
  | exact S 5 125 3 (by decide +kernel)
  | exact S 5 125 4 (by decide +kernel)
  | exact S 5 125 5 (by decide +kernel)
theorem q5_126:ThresholdAt 5 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 126 0 (by decide +kernel)
  | exact S 5 126 1 (by decide +kernel)
  | exact S 5 126 2 (by decide +kernel)
  | exact S 5 126 3 (by decide +kernel)
  | exact S 5 126 4 (by decide +kernel)
  | exact S 5 126 5 (by decide +kernel)
theorem q5_127:ThresholdAt 5 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 127 0 (by decide +kernel)
  | exact S 5 127 1 (by decide +kernel)
  | exact S 5 127 2 (by decide +kernel)
  | exact S 5 127 3 (by decide +kernel)
  | exact S 5 127 4 (by decide +kernel)
  | exact S 5 127 5 (by decide +kernel)
theorem q5_128:ThresholdAt 5 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 128 0 (by decide +kernel)
  | exact S 5 128 1 (by decide +kernel)
  | exact S 5 128 2 (by decide +kernel)
  | exact S 5 128 3 (by decide +kernel)
  | exact S 5 128 4 (by decide +kernel)
  | exact S 5 128 5 (by decide +kernel)
theorem q5_129:ThresholdAt 5 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 129 0 (by decide +kernel)
  | exact S 5 129 1 (by decide +kernel)
  | exact S 5 129 2 (by decide +kernel)
  | exact S 5 129 3 (by decide +kernel)
  | exact S 5 129 4 (by decide +kernel)
  | exact S 5 129 5 (by decide +kernel)
theorem q5_130:ThresholdAt 5 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 130 0 (by decide +kernel)
  | exact S 5 130 1 (by decide +kernel)
  | exact S 5 130 2 (by decide +kernel)
  | exact S 5 130 3 (by decide +kernel)
  | exact S 5 130 4 (by decide +kernel)
  | exact S 5 130 5 (by decide +kernel)
theorem q5_131:ThresholdAt 5 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 131 0 (by decide +kernel)
  | exact S 5 131 1 (by decide +kernel)
  | exact S 5 131 2 (by decide +kernel)
  | exact S 5 131 3 (by decide +kernel)
  | exact S 5 131 4 (by decide +kernel)
  | exact S 5 131 5 (by decide +kernel)
theorem q5_132:ThresholdAt 5 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 132 0 (by decide +kernel)
  | exact S 5 132 1 (by decide +kernel)
  | exact S 5 132 2 (by decide +kernel)
  | exact S 5 132 3 (by decide +kernel)
  | exact S 5 132 4 (by decide +kernel)
  | exact S 5 132 5 (by decide +kernel)
theorem q5_133:ThresholdAt 5 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 133 0 (by decide +kernel)
  | exact S 5 133 1 (by decide +kernel)
  | exact S 5 133 2 (by decide +kernel)
  | exact S 5 133 3 (by decide +kernel)
  | exact S 5 133 4 (by decide +kernel)
  | exact S 5 133 5 (by decide +kernel)
theorem q5_134:ThresholdAt 5 134:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 134 0 (by decide +kernel)
  | exact S 5 134 1 (by decide +kernel)
  | exact S 5 134 2 (by decide +kernel)
  | exact S 5 134 3 (by decide +kernel)
  | exact S 5 134 4 (by decide +kernel)
  | exact S 5 134 5 (by decide +kernel)
theorem q5_135:ThresholdAt 5 135:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 135 0 (by decide +kernel)
  | exact S 5 135 1 (by decide +kernel)
  | exact S 5 135 2 (by decide +kernel)
  | exact S 5 135 3 (by decide +kernel)
  | exact S 5 135 4 (by decide +kernel)
  | exact S 5 135 5 (by decide +kernel)
theorem q5_136:ThresholdAt 5 136:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 136 0 (by decide +kernel)
  | exact S 5 136 1 (by decide +kernel)
  | exact S 5 136 2 (by decide +kernel)
  | exact S 5 136 3 (by decide +kernel)
  | exact S 5 136 4 (by decide +kernel)
  | exact S 5 136 5 (by decide +kernel)
theorem q5_137:ThresholdAt 5 137:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 5 137 0 (by decide +kernel)
  | exact S 5 137 1 (by decide +kernel)
  | exact S 5 137 2 (by decide +kernel)
  | exact S 5 137 3 (by decide +kernel)
  | exact S 5 137 4 (by decide +kernel)
  | exact S 5 137 5 (by decide +kernel)
theorem checkedR5:∀ V ∈ List.range 138,ThresholdAt 5 V:=by
  intro V hV
  have hv:V < 138:=List.mem_range.mp hV
  by_cases h0_138:V < 69
  · by_cases h0_69:V < 34
    · by_cases h0_34:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q5_0
              · have he:V = 1:=by omega
                subst V
                exact q5_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q5_2
              · have he:V = 3:=by omega
                subst V
                exact q5_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q5_4
              · have he:V = 5:=by omega
                subst V
                exact q5_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q5_6
              · have he:V = 7:=by omega
                subst V
                exact q5_7
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q5_8
              · have he:V = 9:=by omega
                subst V
                exact q5_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q5_10
              · have he:V = 11:=by omega
                subst V
                exact q5_11
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q5_12
              · have he:V = 13:=by omega
                subst V
                exact q5_13
            · by_cases h14_17:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q5_14
              · by_cases h15_17:V < 16
                · have he:V = 15:=by omega
                  subst V
                  exact q5_15
                · have he:V = 16:=by omega
                  subst V
                  exact q5_16
      · by_cases h17_34:V < 25
        · by_cases h17_25:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q5_17
              · have he:V = 18:=by omega
                subst V
                exact q5_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q5_19
              · have he:V = 20:=by omega
                subst V
                exact q5_20
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q5_21
              · have he:V = 22:=by omega
                subst V
                exact q5_22
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q5_23
              · have he:V = 24:=by omega
                subst V
                exact q5_24
        · by_cases h25_34:V < 29
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q5_25
              · have he:V = 26:=by omega
                subst V
                exact q5_26
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q5_27
              · have he:V = 28:=by omega
                subst V
                exact q5_28
          · by_cases h29_34:V < 31
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q5_29
              · have he:V = 30:=by omega
                subst V
                exact q5_30
            · by_cases h31_34:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q5_31
              · by_cases h32_34:V < 33
                · have he:V = 32:=by omega
                  subst V
                  exact q5_32
                · have he:V = 33:=by omega
                  subst V
                  exact q5_33
    · by_cases h34_69:V < 51
      · by_cases h34_51:V < 42
        · by_cases h34_42:V < 38
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q5_34
              · have he:V = 35:=by omega
                subst V
                exact q5_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q5_36
              · have he:V = 37:=by omega
                subst V
                exact q5_37
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q5_38
              · have he:V = 39:=by omega
                subst V
                exact q5_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q5_40
              · have he:V = 41:=by omega
                subst V
                exact q5_41
        · by_cases h42_51:V < 46
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q5_42
              · have he:V = 43:=by omega
                subst V
                exact q5_43
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q5_44
              · have he:V = 45:=by omega
                subst V
                exact q5_45
          · by_cases h46_51:V < 48
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q5_46
              · have he:V = 47:=by omega
                subst V
                exact q5_47
            · by_cases h48_51:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q5_48
              · by_cases h49_51:V < 50
                · have he:V = 49:=by omega
                  subst V
                  exact q5_49
                · have he:V = 50:=by omega
                  subst V
                  exact q5_50
      · by_cases h51_69:V < 60
        · by_cases h51_60:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q5_51
              · have he:V = 52:=by omega
                subst V
                exact q5_52
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q5_53
              · have he:V = 54:=by omega
                subst V
                exact q5_54
          · by_cases h55_60:V < 57
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q5_55
              · have he:V = 56:=by omega
                subst V
                exact q5_56
            · by_cases h57_60:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q5_57
              · by_cases h58_60:V < 59
                · have he:V = 58:=by omega
                  subst V
                  exact q5_58
                · have he:V = 59:=by omega
                  subst V
                  exact q5_59
        · by_cases h60_69:V < 64
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q5_60
              · have he:V = 61:=by omega
                subst V
                exact q5_61
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q5_62
              · have he:V = 63:=by omega
                subst V
                exact q5_63
          · by_cases h64_69:V < 66
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q5_64
              · have he:V = 65:=by omega
                subst V
                exact q5_65
            · by_cases h66_69:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q5_66
              · by_cases h67_69:V < 68
                · have he:V = 67:=by omega
                  subst V
                  exact q5_67
                · have he:V = 68:=by omega
                  subst V
                  exact q5_68
  · by_cases h69_138:V < 103
    · by_cases h69_103:V < 86
      · by_cases h69_86:V < 77
        · by_cases h69_77:V < 73
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q5_69
              · have he:V = 70:=by omega
                subst V
                exact q5_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q5_71
              · have he:V = 72:=by omega
                subst V
                exact q5_72
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q5_73
              · have he:V = 74:=by omega
                subst V
                exact q5_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q5_75
              · have he:V = 76:=by omega
                subst V
                exact q5_76
        · by_cases h77_86:V < 81
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q5_77
              · have he:V = 78:=by omega
                subst V
                exact q5_78
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q5_79
              · have he:V = 80:=by omega
                subst V
                exact q5_80
          · by_cases h81_86:V < 83
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q5_81
              · have he:V = 82:=by omega
                subst V
                exact q5_82
            · by_cases h83_86:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q5_83
              · by_cases h84_86:V < 85
                · have he:V = 84:=by omega
                  subst V
                  exact q5_84
                · have he:V = 85:=by omega
                  subst V
                  exact q5_85
      · by_cases h86_103:V < 94
        · by_cases h86_94:V < 90
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q5_86
              · have he:V = 87:=by omega
                subst V
                exact q5_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q5_88
              · have he:V = 89:=by omega
                subst V
                exact q5_89
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q5_90
              · have he:V = 91:=by omega
                subst V
                exact q5_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q5_92
              · have he:V = 93:=by omega
                subst V
                exact q5_93
        · by_cases h94_103:V < 98
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q5_94
              · have he:V = 95:=by omega
                subst V
                exact q5_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q5_96
              · have he:V = 97:=by omega
                subst V
                exact q5_97
          · by_cases h98_103:V < 100
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q5_98
              · have he:V = 99:=by omega
                subst V
                exact q5_99
            · by_cases h100_103:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q5_100
              · by_cases h101_103:V < 102
                · have he:V = 101:=by omega
                  subst V
                  exact q5_101
                · have he:V = 102:=by omega
                  subst V
                  exact q5_102
    · by_cases h103_138:V < 120
      · by_cases h103_120:V < 111
        · by_cases h103_111:V < 107
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q5_103
              · have he:V = 104:=by omega
                subst V
                exact q5_104
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q5_105
              · have he:V = 106:=by omega
                subst V
                exact q5_106
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q5_107
              · have he:V = 108:=by omega
                subst V
                exact q5_108
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q5_109
              · have he:V = 110:=by omega
                subst V
                exact q5_110
        · by_cases h111_120:V < 115
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q5_111
              · have he:V = 112:=by omega
                subst V
                exact q5_112
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q5_113
              · have he:V = 114:=by omega
                subst V
                exact q5_114
          · by_cases h115_120:V < 117
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q5_115
              · have he:V = 116:=by omega
                subst V
                exact q5_116
            · by_cases h117_120:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q5_117
              · by_cases h118_120:V < 119
                · have he:V = 118:=by omega
                  subst V
                  exact q5_118
                · have he:V = 119:=by omega
                  subst V
                  exact q5_119
      · by_cases h120_138:V < 129
        · by_cases h120_129:V < 124
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q5_120
              · have he:V = 121:=by omega
                subst V
                exact q5_121
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q5_122
              · have he:V = 123:=by omega
                subst V
                exact q5_123
          · by_cases h124_129:V < 126
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q5_124
              · have he:V = 125:=by omega
                subst V
                exact q5_125
            · by_cases h126_129:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q5_126
              · by_cases h127_129:V < 128
                · have he:V = 127:=by omega
                  subst V
                  exact q5_127
                · have he:V = 128:=by omega
                  subst V
                  exact q5_128
        · by_cases h129_138:V < 133
          · by_cases h129_133:V < 131
            · by_cases h129_131:V < 130
              · have he:V = 129:=by omega
                subst V
                exact q5_129
              · have he:V = 130:=by omega
                subst V
                exact q5_130
            · by_cases h131_133:V < 132
              · have he:V = 131:=by omega
                subst V
                exact q5_131
              · have he:V = 132:=by omega
                subst V
                exact q5_132
          · by_cases h133_138:V < 135
            · by_cases h133_135:V < 134
              · have he:V = 133:=by omega
                subst V
                exact q5_133
              · have he:V = 134:=by omega
                subst V
                exact q5_134
            · by_cases h135_138:V < 136
              · have he:V = 135:=by omega
                subst V
                exact q5_135
              · by_cases h136_138:V < 137
                · have he:V = 136:=by omega
                  subst V
                  exact q5_136
                · have he:V = 137:=by omega
                  subst V
                  exact q5_137
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
