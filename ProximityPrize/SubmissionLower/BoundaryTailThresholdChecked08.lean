import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked07

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q8_0:ThresholdAt 8 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 0 0 (by decide +kernel)
  | exact S 8 0 1 (by decide +kernel)
  | exact S 8 0 2 (by decide +kernel)
  | exact S 8 0 3 (by decide +kernel)
  | exact S 8 0 4 (by decide +kernel)
  | exact S 8 0 5 (by decide +kernel)
theorem q8_1:ThresholdAt 8 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 1 0 (by decide +kernel)
  | exact S 8 1 1 (by decide +kernel)
  | exact S 8 1 2 (by decide +kernel)
  | exact S 8 1 3 (by decide +kernel)
  | exact S 8 1 4 (by decide +kernel)
  | exact S 8 1 5 (by decide +kernel)
theorem q8_2:ThresholdAt 8 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 2 0 (by decide +kernel)
  | exact S 8 2 1 (by decide +kernel)
  | exact S 8 2 2 (by decide +kernel)
  | exact S 8 2 3 (by decide +kernel)
  | exact S 8 2 4 (by decide +kernel)
  | exact S 8 2 5 (by decide +kernel)
theorem q8_3:ThresholdAt 8 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 3 0 (by decide +kernel)
  | exact S 8 3 1 (by decide +kernel)
  | exact S 8 3 2 (by decide +kernel)
  | exact S 8 3 3 (by decide +kernel)
  | exact S 8 3 4 (by decide +kernel)
  | exact S 8 3 5 (by decide +kernel)
theorem q8_4:ThresholdAt 8 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 4 0 (by decide +kernel)
  | exact S 8 4 1 (by decide +kernel)
  | exact S 8 4 2 (by decide +kernel)
  | exact S 8 4 3 (by decide +kernel)
  | exact S 8 4 4 (by decide +kernel)
  | exact S 8 4 5 (by decide +kernel)
theorem q8_5:ThresholdAt 8 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 5 0 (by decide +kernel)
  | exact S 8 5 1 (by decide +kernel)
  | exact S 8 5 2 (by decide +kernel)
  | exact S 8 5 3 (by decide +kernel)
  | exact S 8 5 4 (by decide +kernel)
  | exact S 8 5 5 (by decide +kernel)
theorem q8_6:ThresholdAt 8 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 6 0 (by decide +kernel)
  | exact S 8 6 1 (by decide +kernel)
  | exact S 8 6 2 (by decide +kernel)
  | exact S 8 6 3 (by decide +kernel)
  | exact S 8 6 4 (by decide +kernel)
  | exact S 8 6 5 (by decide +kernel)
theorem q8_7:ThresholdAt 8 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 7 0 (by decide +kernel)
  | exact S 8 7 1 (by decide +kernel)
  | exact S 8 7 2 (by decide +kernel)
  | exact S 8 7 3 (by decide +kernel)
  | exact S 8 7 4 (by decide +kernel)
  | exact S 8 7 5 (by decide +kernel)
theorem q8_8:ThresholdAt 8 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 8 0 (by decide +kernel)
  | exact S 8 8 1 (by decide +kernel)
  | exact S 8 8 2 (by decide +kernel)
  | exact S 8 8 3 (by decide +kernel)
  | exact S 8 8 4 (by decide +kernel)
  | exact S 8 8 5 (by decide +kernel)
theorem q8_9:ThresholdAt 8 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 9 0 (by decide +kernel)
  | exact S 8 9 1 (by decide +kernel)
  | exact S 8 9 2 (by decide +kernel)
  | exact S 8 9 3 (by decide +kernel)
  | exact S 8 9 4 (by decide +kernel)
  | exact S 8 9 5 (by decide +kernel)
theorem q8_10:ThresholdAt 8 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 10 0 (by decide +kernel)
  | exact S 8 10 1 (by decide +kernel)
  | exact S 8 10 2 (by decide +kernel)
  | exact S 8 10 3 (by decide +kernel)
  | exact S 8 10 4 (by decide +kernel)
  | exact S 8 10 5 (by decide +kernel)
theorem q8_11:ThresholdAt 8 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 11 0 (by decide +kernel)
  | exact S 8 11 1 (by decide +kernel)
  | exact S 8 11 2 (by decide +kernel)
  | exact S 8 11 3 (by decide +kernel)
  | exact S 8 11 4 (by decide +kernel)
  | exact S 8 11 5 (by decide +kernel)
theorem q8_12:ThresholdAt 8 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 12 0 (by decide +kernel)
  | exact S 8 12 1 (by decide +kernel)
  | exact S 8 12 2 (by decide +kernel)
  | exact S 8 12 3 (by decide +kernel)
  | exact S 8 12 4 (by decide +kernel)
  | exact S 8 12 5 (by decide +kernel)
theorem q8_13:ThresholdAt 8 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 13 0 (by decide +kernel)
  | exact S 8 13 1 (by decide +kernel)
  | exact S 8 13 2 (by decide +kernel)
  | exact S 8 13 3 (by decide +kernel)
  | exact S 8 13 4 (by decide +kernel)
  | exact S 8 13 5 (by decide +kernel)
theorem q8_14:ThresholdAt 8 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 14 0 (by decide +kernel)
  | exact S 8 14 1 (by decide +kernel)
  | exact S 8 14 2 (by decide +kernel)
  | exact S 8 14 3 (by decide +kernel)
  | exact S 8 14 4 (by decide +kernel)
  | exact S 8 14 5 (by decide +kernel)
theorem q8_15:ThresholdAt 8 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 15 0 (by decide +kernel)
  | exact S 8 15 1 (by decide +kernel)
  | exact S 8 15 2 (by decide +kernel)
  | exact S 8 15 3 (by decide +kernel)
  | exact S 8 15 4 (by decide +kernel)
  | exact S 8 15 5 (by decide +kernel)
theorem q8_16:ThresholdAt 8 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 16 0 (by decide +kernel)
  | exact S 8 16 1 (by decide +kernel)
  | exact S 8 16 2 (by decide +kernel)
  | exact S 8 16 3 (by decide +kernel)
  | exact S 8 16 4 (by decide +kernel)
  | exact S 8 16 5 (by decide +kernel)
theorem q8_17:ThresholdAt 8 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 17 0 (by decide +kernel)
  | exact S 8 17 1 (by decide +kernel)
  | exact S 8 17 2 (by decide +kernel)
  | exact S 8 17 3 (by decide +kernel)
  | exact S 8 17 4 (by decide +kernel)
  | exact S 8 17 5 (by decide +kernel)
theorem q8_18:ThresholdAt 8 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 18 0 (by decide +kernel)
  | exact S 8 18 1 (by decide +kernel)
  | exact S 8 18 2 (by decide +kernel)
  | exact S 8 18 3 (by decide +kernel)
  | exact S 8 18 4 (by decide +kernel)
  | exact S 8 18 5 (by decide +kernel)
theorem q8_19:ThresholdAt 8 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 19 0 (by decide +kernel)
  | exact S 8 19 1 (by decide +kernel)
  | exact S 8 19 2 (by decide +kernel)
  | exact S 8 19 3 (by decide +kernel)
  | exact S 8 19 4 (by decide +kernel)
  | exact S 8 19 5 (by decide +kernel)
theorem q8_20:ThresholdAt 8 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 20 0 (by decide +kernel)
  | exact S 8 20 1 (by decide +kernel)
  | exact S 8 20 2 (by decide +kernel)
  | exact S 8 20 3 (by decide +kernel)
  | exact S 8 20 4 (by decide +kernel)
  | exact S 8 20 5 (by decide +kernel)
theorem q8_21:ThresholdAt 8 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 21 0 (by decide +kernel)
  | exact S 8 21 1 (by decide +kernel)
  | exact S 8 21 2 (by decide +kernel)
  | exact S 8 21 3 (by decide +kernel)
  | exact S 8 21 4 (by decide +kernel)
  | exact S 8 21 5 (by decide +kernel)
theorem q8_22:ThresholdAt 8 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 22 0 (by decide +kernel)
  | exact S 8 22 1 (by decide +kernel)
  | exact S 8 22 2 (by decide +kernel)
  | exact S 8 22 3 (by decide +kernel)
  | exact S 8 22 4 (by decide +kernel)
  | exact S 8 22 5 (by decide +kernel)
theorem q8_23:ThresholdAt 8 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 23 0 (by decide +kernel)
  | exact S 8 23 1 (by decide +kernel)
  | exact S 8 23 2 (by decide +kernel)
  | exact S 8 23 3 (by decide +kernel)
  | exact S 8 23 4 (by decide +kernel)
  | exact S 8 23 5 (by decide +kernel)
theorem q8_24:ThresholdAt 8 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 24 0 (by decide +kernel)
  | exact S 8 24 1 (by decide +kernel)
  | exact S 8 24 2 (by decide +kernel)
  | exact S 8 24 3 (by decide +kernel)
  | exact S 8 24 4 (by decide +kernel)
  | exact S 8 24 5 (by decide +kernel)
theorem q8_25:ThresholdAt 8 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 25 0 (by decide +kernel)
  | exact S 8 25 1 (by decide +kernel)
  | exact S 8 25 2 (by decide +kernel)
  | exact S 8 25 3 (by decide +kernel)
  | exact S 8 25 4 (by decide +kernel)
  | exact S 8 25 5 (by decide +kernel)
theorem q8_26:ThresholdAt 8 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 26 0 (by decide +kernel)
  | exact S 8 26 1 (by decide +kernel)
  | exact S 8 26 2 (by decide +kernel)
  | exact S 8 26 3 (by decide +kernel)
  | exact S 8 26 4 (by decide +kernel)
  | exact S 8 26 5 (by decide +kernel)
theorem q8_27:ThresholdAt 8 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 27 0 (by decide +kernel)
  | exact S 8 27 1 (by decide +kernel)
  | exact S 8 27 2 (by decide +kernel)
  | exact S 8 27 3 (by decide +kernel)
  | exact S 8 27 4 (by decide +kernel)
  | exact S 8 27 5 (by decide +kernel)
theorem q8_28:ThresholdAt 8 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 28 0 (by decide +kernel)
  | exact S 8 28 1 (by decide +kernel)
  | exact S 8 28 2 (by decide +kernel)
  | exact S 8 28 3 (by decide +kernel)
  | exact S 8 28 4 (by decide +kernel)
  | exact S 8 28 5 (by decide +kernel)
theorem q8_29:ThresholdAt 8 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 29 0 (by decide +kernel)
  | exact S 8 29 1 (by decide +kernel)
  | exact S 8 29 2 (by decide +kernel)
  | exact S 8 29 3 (by decide +kernel)
  | exact S 8 29 4 (by decide +kernel)
  | exact S 8 29 5 (by decide +kernel)
theorem q8_30:ThresholdAt 8 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 30 0 (by decide +kernel)
  | exact S 8 30 1 (by decide +kernel)
  | exact S 8 30 2 (by decide +kernel)
  | exact S 8 30 3 (by decide +kernel)
  | exact S 8 30 4 (by decide +kernel)
  | exact S 8 30 5 (by decide +kernel)
theorem q8_31:ThresholdAt 8 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 31 0 (by decide +kernel)
  | exact S 8 31 1 (by decide +kernel)
  | exact S 8 31 2 (by decide +kernel)
  | exact S 8 31 3 (by decide +kernel)
  | exact S 8 31 4 (by decide +kernel)
  | exact S 8 31 5 (by decide +kernel)
theorem q8_32:ThresholdAt 8 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 32 0 (by decide +kernel)
  | exact S 8 32 1 (by decide +kernel)
  | exact S 8 32 2 (by decide +kernel)
  | exact S 8 32 3 (by decide +kernel)
  | exact S 8 32 4 (by decide +kernel)
  | exact S 8 32 5 (by decide +kernel)
theorem q8_33:ThresholdAt 8 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 33 0 (by decide +kernel)
  | exact S 8 33 1 (by decide +kernel)
  | exact S 8 33 2 (by decide +kernel)
  | exact S 8 33 3 (by decide +kernel)
  | exact S 8 33 4 (by decide +kernel)
  | exact S 8 33 5 (by decide +kernel)
theorem q8_34:ThresholdAt 8 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 34 0 (by decide +kernel)
  | exact S 8 34 1 (by decide +kernel)
  | exact S 8 34 2 (by decide +kernel)
  | exact S 8 34 3 (by decide +kernel)
  | exact S 8 34 4 (by decide +kernel)
  | exact S 8 34 5 (by decide +kernel)
theorem q8_35:ThresholdAt 8 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 35 0 (by decide +kernel)
  | exact S 8 35 1 (by decide +kernel)
  | exact S 8 35 2 (by decide +kernel)
  | exact S 8 35 3 (by decide +kernel)
  | exact S 8 35 4 (by decide +kernel)
  | exact S 8 35 5 (by decide +kernel)
theorem q8_36:ThresholdAt 8 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 36 0 (by decide +kernel)
  | exact S 8 36 1 (by decide +kernel)
  | exact S 8 36 2 (by decide +kernel)
  | exact S 8 36 3 (by decide +kernel)
  | exact S 8 36 4 (by decide +kernel)
  | exact S 8 36 5 (by decide +kernel)
theorem q8_37:ThresholdAt 8 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 37 0 (by decide +kernel)
  | exact S 8 37 1 (by decide +kernel)
  | exact S 8 37 2 (by decide +kernel)
  | exact S 8 37 3 (by decide +kernel)
  | exact S 8 37 4 (by decide +kernel)
  | exact S 8 37 5 (by decide +kernel)
theorem q8_38:ThresholdAt 8 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 38 0 (by decide +kernel)
  | exact S 8 38 1 (by decide +kernel)
  | exact S 8 38 2 (by decide +kernel)
  | exact S 8 38 3 (by decide +kernel)
  | exact S 8 38 4 (by decide +kernel)
  | exact S 8 38 5 (by decide +kernel)
theorem q8_39:ThresholdAt 8 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 39 0 (by decide +kernel)
  | exact S 8 39 1 (by decide +kernel)
  | exact S 8 39 2 (by decide +kernel)
  | exact S 8 39 3 (by decide +kernel)
  | exact S 8 39 4 (by decide +kernel)
  | exact S 8 39 5 (by decide +kernel)
theorem q8_40:ThresholdAt 8 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 40 0 (by decide +kernel)
  | exact S 8 40 1 (by decide +kernel)
  | exact S 8 40 2 (by decide +kernel)
  | exact S 8 40 3 (by decide +kernel)
  | exact S 8 40 4 (by decide +kernel)
  | exact S 8 40 5 (by decide +kernel)
theorem q8_41:ThresholdAt 8 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 41 0 (by decide +kernel)
  | exact S 8 41 1 (by decide +kernel)
  | exact S 8 41 2 (by decide +kernel)
  | exact S 8 41 3 (by decide +kernel)
  | exact S 8 41 4 (by decide +kernel)
  | exact S 8 41 5 (by decide +kernel)
theorem q8_42:ThresholdAt 8 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 42 0 (by decide +kernel)
  | exact S 8 42 1 (by decide +kernel)
  | exact S 8 42 2 (by decide +kernel)
  | exact S 8 42 3 (by decide +kernel)
  | exact S 8 42 4 (by decide +kernel)
  | exact S 8 42 5 (by decide +kernel)
theorem q8_43:ThresholdAt 8 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 43 0 (by decide +kernel)
  | exact S 8 43 1 (by decide +kernel)
  | exact S 8 43 2 (by decide +kernel)
  | exact S 8 43 3 (by decide +kernel)
  | exact S 8 43 4 (by decide +kernel)
  | exact S 8 43 5 (by decide +kernel)
theorem q8_44:ThresholdAt 8 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 44 0 (by decide +kernel)
  | exact S 8 44 1 (by decide +kernel)
  | exact S 8 44 2 (by decide +kernel)
  | exact S 8 44 3 (by decide +kernel)
  | exact S 8 44 4 (by decide +kernel)
  | exact S 8 44 5 (by decide +kernel)
theorem q8_45:ThresholdAt 8 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 45 0 (by decide +kernel)
  | exact S 8 45 1 (by decide +kernel)
  | exact S 8 45 2 (by decide +kernel)
  | exact S 8 45 3 (by decide +kernel)
  | exact S 8 45 4 (by decide +kernel)
  | exact S 8 45 5 (by decide +kernel)
theorem q8_46:ThresholdAt 8 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 46 0 (by decide +kernel)
  | exact S 8 46 1 (by decide +kernel)
  | exact S 8 46 2 (by decide +kernel)
  | exact S 8 46 3 (by decide +kernel)
  | exact S 8 46 4 (by decide +kernel)
  | exact S 8 46 5 (by decide +kernel)
theorem q8_47:ThresholdAt 8 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 47 0 (by decide +kernel)
  | exact S 8 47 1 (by decide +kernel)
  | exact S 8 47 2 (by decide +kernel)
  | exact S 8 47 3 (by decide +kernel)
  | exact S 8 47 4 (by decide +kernel)
  | exact S 8 47 5 (by decide +kernel)
theorem q8_48:ThresholdAt 8 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 48 0 (by decide +kernel)
  | exact S 8 48 1 (by decide +kernel)
  | exact S 8 48 2 (by decide +kernel)
  | exact S 8 48 3 (by decide +kernel)
  | exact S 8 48 4 (by decide +kernel)
  | exact S 8 48 5 (by decide +kernel)
theorem q8_49:ThresholdAt 8 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 49 0 (by decide +kernel)
  | exact S 8 49 1 (by decide +kernel)
  | exact S 8 49 2 (by decide +kernel)
  | exact S 8 49 3 (by decide +kernel)
  | exact S 8 49 4 (by decide +kernel)
  | exact S 8 49 5 (by decide +kernel)
theorem q8_50:ThresholdAt 8 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 50 0 (by decide +kernel)
  | exact S 8 50 1 (by decide +kernel)
  | exact S 8 50 2 (by decide +kernel)
  | exact S 8 50 3 (by decide +kernel)
  | exact S 8 50 4 (by decide +kernel)
  | exact S 8 50 5 (by decide +kernel)
theorem q8_51:ThresholdAt 8 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 51 0 (by decide +kernel)
  | exact S 8 51 1 (by decide +kernel)
  | exact S 8 51 2 (by decide +kernel)
  | exact S 8 51 3 (by decide +kernel)
  | exact S 8 51 4 (by decide +kernel)
  | exact S 8 51 5 (by decide +kernel)
theorem q8_52:ThresholdAt 8 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 52 0 (by decide +kernel)
  | exact S 8 52 1 (by decide +kernel)
  | exact S 8 52 2 (by decide +kernel)
  | exact S 8 52 3 (by decide +kernel)
  | exact S 8 52 4 (by decide +kernel)
  | exact S 8 52 5 (by decide +kernel)
theorem q8_53:ThresholdAt 8 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 53 0 (by decide +kernel)
  | exact S 8 53 1 (by decide +kernel)
  | exact S 8 53 2 (by decide +kernel)
  | exact S 8 53 3 (by decide +kernel)
  | exact S 8 53 4 (by decide +kernel)
  | exact S 8 53 5 (by decide +kernel)
theorem q8_54:ThresholdAt 8 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 54 0 (by decide +kernel)
  | exact S 8 54 1 (by decide +kernel)
  | exact S 8 54 2 (by decide +kernel)
  | exact S 8 54 3 (by decide +kernel)
  | exact S 8 54 4 (by decide +kernel)
  | exact S 8 54 5 (by decide +kernel)
theorem q8_55:ThresholdAt 8 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 55 0 (by decide +kernel)
  | exact S 8 55 1 (by decide +kernel)
  | exact S 8 55 2 (by decide +kernel)
  | exact S 8 55 3 (by decide +kernel)
  | exact S 8 55 4 (by decide +kernel)
  | exact S 8 55 5 (by decide +kernel)
theorem q8_56:ThresholdAt 8 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 56 0 (by decide +kernel)
  | exact S 8 56 1 (by decide +kernel)
  | exact S 8 56 2 (by decide +kernel)
  | exact S 8 56 3 (by decide +kernel)
  | exact S 8 56 4 (by decide +kernel)
  | exact S 8 56 5 (by decide +kernel)
theorem q8_57:ThresholdAt 8 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 57 0 (by decide +kernel)
  | exact S 8 57 1 (by decide +kernel)
  | exact S 8 57 2 (by decide +kernel)
  | exact S 8 57 3 (by decide +kernel)
  | exact S 8 57 4 (by decide +kernel)
  | exact S 8 57 5 (by decide +kernel)
theorem q8_58:ThresholdAt 8 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 58 0 (by decide +kernel)
  | exact S 8 58 1 (by decide +kernel)
  | exact S 8 58 2 (by decide +kernel)
  | exact S 8 58 3 (by decide +kernel)
  | exact S 8 58 4 (by decide +kernel)
  | exact S 8 58 5 (by decide +kernel)
theorem q8_59:ThresholdAt 8 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 59 0 (by decide +kernel)
  | exact S 8 59 1 (by decide +kernel)
  | exact S 8 59 2 (by decide +kernel)
  | exact S 8 59 3 (by decide +kernel)
  | exact S 8 59 4 (by decide +kernel)
  | exact S 8 59 5 (by decide +kernel)
theorem q8_60:ThresholdAt 8 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 60 0 (by decide +kernel)
  | exact S 8 60 1 (by decide +kernel)
  | exact S 8 60 2 (by decide +kernel)
  | exact S 8 60 3 (by decide +kernel)
  | exact S 8 60 4 (by decide +kernel)
  | exact S 8 60 5 (by decide +kernel)
theorem q8_61:ThresholdAt 8 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 61 0 (by decide +kernel)
  | exact S 8 61 1 (by decide +kernel)
  | exact S 8 61 2 (by decide +kernel)
  | exact S 8 61 3 (by decide +kernel)
  | exact S 8 61 4 (by decide +kernel)
  | exact S 8 61 5 (by decide +kernel)
theorem q8_62:ThresholdAt 8 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 62 0 (by decide +kernel)
  | exact S 8 62 1 (by decide +kernel)
  | exact S 8 62 2 (by decide +kernel)
  | exact S 8 62 3 (by decide +kernel)
  | exact S 8 62 4 (by decide +kernel)
  | exact S 8 62 5 (by decide +kernel)
theorem q8_63:ThresholdAt 8 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 63 0 (by decide +kernel)
  | exact S 8 63 1 (by decide +kernel)
  | exact S 8 63 2 (by decide +kernel)
  | exact S 8 63 3 (by decide +kernel)
  | exact S 8 63 4 (by decide +kernel)
  | exact S 8 63 5 (by decide +kernel)
theorem q8_64:ThresholdAt 8 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 64 0 (by decide +kernel)
  | exact S 8 64 1 (by decide +kernel)
  | exact S 8 64 2 (by decide +kernel)
  | exact S 8 64 3 (by decide +kernel)
  | exact S 8 64 4 (by decide +kernel)
  | exact S 8 64 5 (by decide +kernel)
theorem q8_65:ThresholdAt 8 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 65 0 (by decide +kernel)
  | exact S 8 65 1 (by decide +kernel)
  | exact S 8 65 2 (by decide +kernel)
  | exact S 8 65 3 (by decide +kernel)
  | exact S 8 65 4 (by decide +kernel)
  | exact S 8 65 5 (by decide +kernel)
theorem q8_66:ThresholdAt 8 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 66 0 (by decide +kernel)
  | exact S 8 66 1 (by decide +kernel)
  | exact S 8 66 2 (by decide +kernel)
  | exact S 8 66 3 (by decide +kernel)
  | exact S 8 66 4 (by decide +kernel)
  | exact S 8 66 5 (by decide +kernel)
theorem q8_67:ThresholdAt 8 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 67 0 (by decide +kernel)
  | exact S 8 67 1 (by decide +kernel)
  | exact S 8 67 2 (by decide +kernel)
  | exact S 8 67 3 (by decide +kernel)
  | exact S 8 67 4 (by decide +kernel)
  | exact S 8 67 5 (by decide +kernel)
theorem q8_68:ThresholdAt 8 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 68 0 (by decide +kernel)
  | exact S 8 68 1 (by decide +kernel)
  | exact S 8 68 2 (by decide +kernel)
  | exact S 8 68 3 (by decide +kernel)
  | exact S 8 68 4 (by decide +kernel)
  | exact S 8 68 5 (by decide +kernel)
theorem q8_69:ThresholdAt 8 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 69 0 (by decide +kernel)
  | exact S 8 69 1 (by decide +kernel)
  | exact S 8 69 2 (by decide +kernel)
  | exact S 8 69 3 (by decide +kernel)
  | exact S 8 69 4 (by decide +kernel)
  | exact S 8 69 5 (by decide +kernel)
theorem q8_70:ThresholdAt 8 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 70 0 (by decide +kernel)
  | exact S 8 70 1 (by decide +kernel)
  | exact S 8 70 2 (by decide +kernel)
  | exact S 8 70 3 (by decide +kernel)
  | exact S 8 70 4 (by decide +kernel)
  | exact S 8 70 5 (by decide +kernel)
theorem q8_71:ThresholdAt 8 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 71 0 (by decide +kernel)
  | exact S 8 71 1 (by decide +kernel)
  | exact S 8 71 2 (by decide +kernel)
  | exact S 8 71 3 (by decide +kernel)
  | exact S 8 71 4 (by decide +kernel)
  | exact S 8 71 5 (by decide +kernel)
theorem q8_72:ThresholdAt 8 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 72 0 (by decide +kernel)
  | exact S 8 72 1 (by decide +kernel)
  | exact S 8 72 2 (by decide +kernel)
  | exact S 8 72 3 (by decide +kernel)
  | exact S 8 72 4 (by decide +kernel)
  | exact S 8 72 5 (by decide +kernel)
theorem q8_73:ThresholdAt 8 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 73 0 (by decide +kernel)
  | exact S 8 73 1 (by decide +kernel)
  | exact S 8 73 2 (by decide +kernel)
  | exact S 8 73 3 (by decide +kernel)
  | exact S 8 73 4 (by decide +kernel)
  | exact S 8 73 5 (by decide +kernel)
theorem q8_74:ThresholdAt 8 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 74 0 (by decide +kernel)
  | exact S 8 74 1 (by decide +kernel)
  | exact S 8 74 2 (by decide +kernel)
  | exact S 8 74 3 (by decide +kernel)
  | exact S 8 74 4 (by decide +kernel)
  | exact S 8 74 5 (by decide +kernel)
theorem q8_75:ThresholdAt 8 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 75 0 (by decide +kernel)
  | exact S 8 75 1 (by decide +kernel)
  | exact S 8 75 2 (by decide +kernel)
  | exact S 8 75 3 (by decide +kernel)
  | exact S 8 75 4 (by decide +kernel)
  | exact S 8 75 5 (by decide +kernel)
theorem q8_76:ThresholdAt 8 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 76 0 (by decide +kernel)
  | exact S 8 76 1 (by decide +kernel)
  | exact S 8 76 2 (by decide +kernel)
  | exact S 8 76 3 (by decide +kernel)
  | exact S 8 76 4 (by decide +kernel)
  | exact S 8 76 5 (by decide +kernel)
theorem q8_77:ThresholdAt 8 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 77 0 (by decide +kernel)
  | exact S 8 77 1 (by decide +kernel)
  | exact S 8 77 2 (by decide +kernel)
  | exact S 8 77 3 (by decide +kernel)
  | exact S 8 77 4 (by decide +kernel)
  | exact S 8 77 5 (by decide +kernel)
theorem q8_78:ThresholdAt 8 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 78 0 (by decide +kernel)
  | exact S 8 78 1 (by decide +kernel)
  | exact S 8 78 2 (by decide +kernel)
  | exact S 8 78 3 (by decide +kernel)
  | exact S 8 78 4 (by decide +kernel)
  | exact S 8 78 5 (by decide +kernel)
theorem q8_79:ThresholdAt 8 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 79 0 (by decide +kernel)
  | exact S 8 79 1 (by decide +kernel)
  | exact S 8 79 2 (by decide +kernel)
  | exact S 8 79 3 (by decide +kernel)
  | exact S 8 79 4 (by decide +kernel)
  | exact S 8 79 5 (by decide +kernel)
theorem q8_80:ThresholdAt 8 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 80 0 (by decide +kernel)
  | exact S 8 80 1 (by decide +kernel)
  | exact S 8 80 2 (by decide +kernel)
  | exact S 8 80 3 (by decide +kernel)
  | exact S 8 80 4 (by decide +kernel)
  | exact S 8 80 5 (by decide +kernel)
theorem q8_81:ThresholdAt 8 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 81 0 (by decide +kernel)
  | exact S 8 81 1 (by decide +kernel)
  | exact S 8 81 2 (by decide +kernel)
  | exact S 8 81 3 (by decide +kernel)
  | exact S 8 81 4 (by decide +kernel)
  | exact S 8 81 5 (by decide +kernel)
theorem q8_82:ThresholdAt 8 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 82 0 (by decide +kernel)
  | exact S 8 82 1 (by decide +kernel)
  | exact S 8 82 2 (by decide +kernel)
  | exact S 8 82 3 (by decide +kernel)
  | exact S 8 82 4 (by decide +kernel)
  | exact S 8 82 5 (by decide +kernel)
theorem q8_83:ThresholdAt 8 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 83 0 (by decide +kernel)
  | exact S 8 83 1 (by decide +kernel)
  | exact S 8 83 2 (by decide +kernel)
  | exact S 8 83 3 (by decide +kernel)
  | exact S 8 83 4 (by decide +kernel)
  | exact S 8 83 5 (by decide +kernel)
theorem q8_84:ThresholdAt 8 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 84 0 (by decide +kernel)
  | exact S 8 84 1 (by decide +kernel)
  | exact S 8 84 2 (by decide +kernel)
  | exact S 8 84 3 (by decide +kernel)
  | exact S 8 84 4 (by decide +kernel)
  | exact S 8 84 5 (by decide +kernel)
theorem q8_85:ThresholdAt 8 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 85 0 (by decide +kernel)
  | exact S 8 85 1 (by decide +kernel)
  | exact S 8 85 2 (by decide +kernel)
  | exact S 8 85 3 (by decide +kernel)
  | exact S 8 85 4 (by decide +kernel)
  | exact S 8 85 5 (by decide +kernel)
theorem q8_86:ThresholdAt 8 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 86 0 (by decide +kernel)
  | exact S 8 86 1 (by decide +kernel)
  | exact S 8 86 2 (by decide +kernel)
  | exact S 8 86 3 (by decide +kernel)
  | exact S 8 86 4 (by decide +kernel)
  | exact S 8 86 5 (by decide +kernel)
theorem q8_87:ThresholdAt 8 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 87 0 (by decide +kernel)
  | exact S 8 87 1 (by decide +kernel)
  | exact S 8 87 2 (by decide +kernel)
  | exact S 8 87 3 (by decide +kernel)
  | exact S 8 87 4 (by decide +kernel)
  | exact S 8 87 5 (by decide +kernel)
theorem q8_88:ThresholdAt 8 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 88 0 (by decide +kernel)
  | exact S 8 88 1 (by decide +kernel)
  | exact S 8 88 2 (by decide +kernel)
  | exact S 8 88 3 (by decide +kernel)
  | exact S 8 88 4 (by decide +kernel)
  | exact S 8 88 5 (by decide +kernel)
theorem q8_89:ThresholdAt 8 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 89 0 (by decide +kernel)
  | exact S 8 89 1 (by decide +kernel)
  | exact S 8 89 2 (by decide +kernel)
  | exact S 8 89 3 (by decide +kernel)
  | exact S 8 89 4 (by decide +kernel)
  | exact S 8 89 5 (by decide +kernel)
theorem q8_90:ThresholdAt 8 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 90 0 (by decide +kernel)
  | exact S 8 90 1 (by decide +kernel)
  | exact S 8 90 2 (by decide +kernel)
  | exact S 8 90 3 (by decide +kernel)
  | exact S 8 90 4 (by decide +kernel)
  | exact S 8 90 5 (by decide +kernel)
theorem q8_91:ThresholdAt 8 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 91 0 (by decide +kernel)
  | exact S 8 91 1 (by decide +kernel)
  | exact S 8 91 2 (by decide +kernel)
  | exact S 8 91 3 (by decide +kernel)
  | exact S 8 91 4 (by decide +kernel)
  | exact S 8 91 5 (by decide +kernel)
theorem q8_92:ThresholdAt 8 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 92 0 (by decide +kernel)
  | exact S 8 92 1 (by decide +kernel)
  | exact S 8 92 2 (by decide +kernel)
  | exact S 8 92 3 (by decide +kernel)
  | exact S 8 92 4 (by decide +kernel)
  | exact S 8 92 5 (by decide +kernel)
theorem q8_93:ThresholdAt 8 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 93 0 (by decide +kernel)
  | exact S 8 93 1 (by decide +kernel)
  | exact S 8 93 2 (by decide +kernel)
  | exact S 8 93 3 (by decide +kernel)
  | exact S 8 93 4 (by decide +kernel)
  | exact S 8 93 5 (by decide +kernel)
theorem q8_94:ThresholdAt 8 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 94 0 (by decide +kernel)
  | exact S 8 94 1 (by decide +kernel)
  | exact S 8 94 2 (by decide +kernel)
  | exact S 8 94 3 (by decide +kernel)
  | exact S 8 94 4 (by decide +kernel)
  | exact S 8 94 5 (by decide +kernel)
theorem q8_95:ThresholdAt 8 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 95 0 (by decide +kernel)
  | exact S 8 95 1 (by decide +kernel)
  | exact S 8 95 2 (by decide +kernel)
  | exact S 8 95 3 (by decide +kernel)
  | exact S 8 95 4 (by decide +kernel)
  | exact S 8 95 5 (by decide +kernel)
theorem q8_96:ThresholdAt 8 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 96 0 (by decide +kernel)
  | exact S 8 96 1 (by decide +kernel)
  | exact S 8 96 2 (by decide +kernel)
  | exact S 8 96 3 (by decide +kernel)
  | exact S 8 96 4 (by decide +kernel)
  | exact S 8 96 5 (by decide +kernel)
theorem q8_97:ThresholdAt 8 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 97 0 (by decide +kernel)
  | exact S 8 97 1 (by decide +kernel)
  | exact S 8 97 2 (by decide +kernel)
  | exact S 8 97 3 (by decide +kernel)
  | exact S 8 97 4 (by decide +kernel)
  | exact S 8 97 5 (by decide +kernel)
theorem q8_98:ThresholdAt 8 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 98 0 (by decide +kernel)
  | exact S 8 98 1 (by decide +kernel)
  | exact S 8 98 2 (by decide +kernel)
  | exact S 8 98 3 (by decide +kernel)
  | exact S 8 98 4 (by decide +kernel)
  | exact S 8 98 5 (by decide +kernel)
theorem q8_99:ThresholdAt 8 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 99 0 (by decide +kernel)
  | exact S 8 99 1 (by decide +kernel)
  | exact S 8 99 2 (by decide +kernel)
  | exact S 8 99 3 (by decide +kernel)
  | exact S 8 99 4 (by decide +kernel)
  | exact S 8 99 5 (by decide +kernel)
theorem q8_100:ThresholdAt 8 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 100 0 (by decide +kernel)
  | exact S 8 100 1 (by decide +kernel)
  | exact S 8 100 2 (by decide +kernel)
  | exact S 8 100 3 (by decide +kernel)
  | exact S 8 100 4 (by decide +kernel)
  | exact S 8 100 5 (by decide +kernel)
theorem q8_101:ThresholdAt 8 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 101 0 (by decide +kernel)
  | exact S 8 101 1 (by decide +kernel)
  | exact S 8 101 2 (by decide +kernel)
  | exact S 8 101 3 (by decide +kernel)
  | exact S 8 101 4 (by decide +kernel)
  | exact S 8 101 5 (by decide +kernel)
theorem q8_102:ThresholdAt 8 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 102 0 (by decide +kernel)
  | exact S 8 102 1 (by decide +kernel)
  | exact S 8 102 2 (by decide +kernel)
  | exact S 8 102 3 (by decide +kernel)
  | exact S 8 102 4 (by decide +kernel)
  | exact S 8 102 5 (by decide +kernel)
theorem q8_103:ThresholdAt 8 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 103 0 (by decide +kernel)
  | exact S 8 103 1 (by decide +kernel)
  | exact S 8 103 2 (by decide +kernel)
  | exact S 8 103 3 (by decide +kernel)
  | exact S 8 103 4 (by decide +kernel)
  | exact S 8 103 5 (by decide +kernel)
theorem q8_104:ThresholdAt 8 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 104 0 (by decide +kernel)
  | exact S 8 104 1 (by decide +kernel)
  | exact S 8 104 2 (by decide +kernel)
  | exact S 8 104 3 (by decide +kernel)
  | exact S 8 104 4 (by decide +kernel)
  | exact S 8 104 5 (by decide +kernel)
theorem q8_105:ThresholdAt 8 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 105 0 (by decide +kernel)
  | exact S 8 105 1 (by decide +kernel)
  | exact S 8 105 2 (by decide +kernel)
  | exact S 8 105 3 (by decide +kernel)
  | exact S 8 105 4 (by decide +kernel)
  | exact S 8 105 5 (by decide +kernel)
theorem q8_106:ThresholdAt 8 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 106 0 (by decide +kernel)
  | exact S 8 106 1 (by decide +kernel)
  | exact S 8 106 2 (by decide +kernel)
  | exact S 8 106 3 (by decide +kernel)
  | exact S 8 106 4 (by decide +kernel)
  | exact S 8 106 5 (by decide +kernel)
theorem q8_107:ThresholdAt 8 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 107 0 (by decide +kernel)
  | exact S 8 107 1 (by decide +kernel)
  | exact S 8 107 2 (by decide +kernel)
  | exact S 8 107 3 (by decide +kernel)
  | exact S 8 107 4 (by decide +kernel)
  | exact S 8 107 5 (by decide +kernel)
theorem q8_108:ThresholdAt 8 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 108 0 (by decide +kernel)
  | exact S 8 108 1 (by decide +kernel)
  | exact S 8 108 2 (by decide +kernel)
  | exact S 8 108 3 (by decide +kernel)
  | exact S 8 108 4 (by decide +kernel)
  | exact S 8 108 5 (by decide +kernel)
theorem q8_109:ThresholdAt 8 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 109 0 (by decide +kernel)
  | exact S 8 109 1 (by decide +kernel)
  | exact S 8 109 2 (by decide +kernel)
  | exact S 8 109 3 (by decide +kernel)
  | exact S 8 109 4 (by decide +kernel)
  | exact S 8 109 5 (by decide +kernel)
theorem q8_110:ThresholdAt 8 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 110 0 (by decide +kernel)
  | exact S 8 110 1 (by decide +kernel)
  | exact S 8 110 2 (by decide +kernel)
  | exact S 8 110 3 (by decide +kernel)
  | exact S 8 110 4 (by decide +kernel)
  | exact S 8 110 5 (by decide +kernel)
theorem q8_111:ThresholdAt 8 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 111 0 (by decide +kernel)
  | exact S 8 111 1 (by decide +kernel)
  | exact S 8 111 2 (by decide +kernel)
  | exact S 8 111 3 (by decide +kernel)
  | exact S 8 111 4 (by decide +kernel)
  | exact S 8 111 5 (by decide +kernel)
theorem q8_112:ThresholdAt 8 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 112 0 (by decide +kernel)
  | exact S 8 112 1 (by decide +kernel)
  | exact S 8 112 2 (by decide +kernel)
  | exact S 8 112 3 (by decide +kernel)
  | exact S 8 112 4 (by decide +kernel)
  | exact S 8 112 5 (by decide +kernel)
theorem q8_113:ThresholdAt 8 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 113 0 (by decide +kernel)
  | exact S 8 113 1 (by decide +kernel)
  | exact S 8 113 2 (by decide +kernel)
  | exact S 8 113 3 (by decide +kernel)
  | exact S 8 113 4 (by decide +kernel)
  | exact S 8 113 5 (by decide +kernel)
theorem q8_114:ThresholdAt 8 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 114 0 (by decide +kernel)
  | exact S 8 114 1 (by decide +kernel)
  | exact S 8 114 2 (by decide +kernel)
  | exact S 8 114 3 (by decide +kernel)
  | exact S 8 114 4 (by decide +kernel)
  | exact S 8 114 5 (by decide +kernel)
theorem q8_115:ThresholdAt 8 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 115 0 (by decide +kernel)
  | exact S 8 115 1 (by decide +kernel)
  | exact S 8 115 2 (by decide +kernel)
  | exact S 8 115 3 (by decide +kernel)
  | exact S 8 115 4 (by decide +kernel)
  | exact S 8 115 5 (by decide +kernel)
theorem q8_116:ThresholdAt 8 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 116 0 (by decide +kernel)
  | exact S 8 116 1 (by decide +kernel)
  | exact S 8 116 2 (by decide +kernel)
  | exact S 8 116 3 (by decide +kernel)
  | exact S 8 116 4 (by decide +kernel)
  | exact S 8 116 5 (by decide +kernel)
theorem q8_117:ThresholdAt 8 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 117 0 (by decide +kernel)
  | exact S 8 117 1 (by decide +kernel)
  | exact S 8 117 2 (by decide +kernel)
  | exact S 8 117 3 (by decide +kernel)
  | exact S 8 117 4 (by decide +kernel)
  | exact S 8 117 5 (by decide +kernel)
theorem q8_118:ThresholdAt 8 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 118 0 (by decide +kernel)
  | exact S 8 118 1 (by decide +kernel)
  | exact S 8 118 2 (by decide +kernel)
  | exact S 8 118 3 (by decide +kernel)
  | exact S 8 118 4 (by decide +kernel)
  | exact S 8 118 5 (by decide +kernel)
theorem q8_119:ThresholdAt 8 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 119 0 (by decide +kernel)
  | exact S 8 119 1 (by decide +kernel)
  | exact S 8 119 2 (by decide +kernel)
  | exact S 8 119 3 (by decide +kernel)
  | exact S 8 119 4 (by decide +kernel)
  | exact S 8 119 5 (by decide +kernel)
theorem q8_120:ThresholdAt 8 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 120 0 (by decide +kernel)
  | exact S 8 120 1 (by decide +kernel)
  | exact S 8 120 2 (by decide +kernel)
  | exact S 8 120 3 (by decide +kernel)
  | exact S 8 120 4 (by decide +kernel)
  | exact S 8 120 5 (by decide +kernel)
theorem q8_121:ThresholdAt 8 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 121 0 (by decide +kernel)
  | exact S 8 121 1 (by decide +kernel)
  | exact S 8 121 2 (by decide +kernel)
  | exact S 8 121 3 (by decide +kernel)
  | exact S 8 121 4 (by decide +kernel)
  | exact S 8 121 5 (by decide +kernel)
theorem q8_122:ThresholdAt 8 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 122 0 (by decide +kernel)
  | exact S 8 122 1 (by decide +kernel)
  | exact S 8 122 2 (by decide +kernel)
  | exact S 8 122 3 (by decide +kernel)
  | exact S 8 122 4 (by decide +kernel)
  | exact S 8 122 5 (by decide +kernel)
theorem q8_123:ThresholdAt 8 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 123 0 (by decide +kernel)
  | exact S 8 123 1 (by decide +kernel)
  | exact S 8 123 2 (by decide +kernel)
  | exact S 8 123 3 (by decide +kernel)
  | exact S 8 123 4 (by decide +kernel)
  | exact S 8 123 5 (by decide +kernel)
theorem q8_124:ThresholdAt 8 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 124 0 (by decide +kernel)
  | exact S 8 124 1 (by decide +kernel)
  | exact S 8 124 2 (by decide +kernel)
  | exact S 8 124 3 (by decide +kernel)
  | exact S 8 124 4 (by decide +kernel)
  | exact S 8 124 5 (by decide +kernel)
theorem q8_125:ThresholdAt 8 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 125 0 (by decide +kernel)
  | exact S 8 125 1 (by decide +kernel)
  | exact S 8 125 2 (by decide +kernel)
  | exact S 8 125 3 (by decide +kernel)
  | exact S 8 125 4 (by decide +kernel)
  | exact S 8 125 5 (by decide +kernel)
theorem q8_126:ThresholdAt 8 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 126 0 (by decide +kernel)
  | exact S 8 126 1 (by decide +kernel)
  | exact S 8 126 2 (by decide +kernel)
  | exact S 8 126 3 (by decide +kernel)
  | exact S 8 126 4 (by decide +kernel)
  | exact S 8 126 5 (by decide +kernel)
theorem q8_127:ThresholdAt 8 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 127 0 (by decide +kernel)
  | exact S 8 127 1 (by decide +kernel)
  | exact S 8 127 2 (by decide +kernel)
  | exact S 8 127 3 (by decide +kernel)
  | exact S 8 127 4 (by decide +kernel)
  | exact S 8 127 5 (by decide +kernel)
theorem q8_128:ThresholdAt 8 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 128 0 (by decide +kernel)
  | exact S 8 128 1 (by decide +kernel)
  | exact S 8 128 2 (by decide +kernel)
  | exact S 8 128 3 (by decide +kernel)
  | exact S 8 128 4 (by decide +kernel)
  | exact S 8 128 5 (by decide +kernel)
theorem q8_129:ThresholdAt 8 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 129 0 (by decide +kernel)
  | exact S 8 129 1 (by decide +kernel)
  | exact S 8 129 2 (by decide +kernel)
  | exact S 8 129 3 (by decide +kernel)
  | exact S 8 129 4 (by decide +kernel)
  | exact S 8 129 5 (by decide +kernel)
theorem q8_130:ThresholdAt 8 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 130 0 (by decide +kernel)
  | exact S 8 130 1 (by decide +kernel)
  | exact S 8 130 2 (by decide +kernel)
  | exact S 8 130 3 (by decide +kernel)
  | exact S 8 130 4 (by decide +kernel)
  | exact S 8 130 5 (by decide +kernel)
theorem q8_131:ThresholdAt 8 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 131 0 (by decide +kernel)
  | exact S 8 131 1 (by decide +kernel)
  | exact S 8 131 2 (by decide +kernel)
  | exact S 8 131 3 (by decide +kernel)
  | exact S 8 131 4 (by decide +kernel)
  | exact S 8 131 5 (by decide +kernel)
theorem q8_132:ThresholdAt 8 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 132 0 (by decide +kernel)
  | exact S 8 132 1 (by decide +kernel)
  | exact S 8 132 2 (by decide +kernel)
  | exact S 8 132 3 (by decide +kernel)
  | exact S 8 132 4 (by decide +kernel)
  | exact S 8 132 5 (by decide +kernel)
theorem q8_133:ThresholdAt 8 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 133 0 (by decide +kernel)
  | exact S 8 133 1 (by decide +kernel)
  | exact S 8 133 2 (by decide +kernel)
  | exact S 8 133 3 (by decide +kernel)
  | exact S 8 133 4 (by decide +kernel)
  | exact S 8 133 5 (by decide +kernel)
theorem q8_134:ThresholdAt 8 134:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 8 134 0 (by decide +kernel)
  | exact S 8 134 1 (by decide +kernel)
  | exact S 8 134 2 (by decide +kernel)
  | exact S 8 134 3 (by decide +kernel)
  | exact S 8 134 4 (by decide +kernel)
  | exact S 8 134 5 (by decide +kernel)
theorem checkedR8:∀ V ∈ List.range 135,ThresholdAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0_135:V < 67
  · by_cases h0_67:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q8_0
              · have he:V = 1:=by omega
                subst V
                exact q8_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q8_2
              · have he:V = 3:=by omega
                subst V
                exact q8_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q8_4
              · have he:V = 5:=by omega
                subst V
                exact q8_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q8_6
              · have he:V = 7:=by omega
                subst V
                exact q8_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q8_8
              · have he:V = 9:=by omega
                subst V
                exact q8_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q8_10
              · have he:V = 11:=by omega
                subst V
                exact q8_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q8_12
              · have he:V = 13:=by omega
                subst V
                exact q8_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q8_14
              · have he:V = 15:=by omega
                subst V
                exact q8_15
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q8_16
              · have he:V = 17:=by omega
                subst V
                exact q8_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q8_18
              · have he:V = 19:=by omega
                subst V
                exact q8_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q8_20
              · have he:V = 21:=by omega
                subst V
                exact q8_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q8_22
              · have he:V = 23:=by omega
                subst V
                exact q8_23
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q8_24
              · have he:V = 25:=by omega
                subst V
                exact q8_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q8_26
              · have he:V = 27:=by omega
                subst V
                exact q8_27
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q8_28
              · have he:V = 29:=by omega
                subst V
                exact q8_29
            · by_cases h30_33:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q8_30
              · by_cases h31_33:V < 32
                · have he:V = 31:=by omega
                  subst V
                  exact q8_31
                · have he:V = 32:=by omega
                  subst V
                  exact q8_32
    · by_cases h33_67:V < 50
      · by_cases h33_50:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q8_33
              · have he:V = 34:=by omega
                subst V
                exact q8_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q8_35
              · have he:V = 36:=by omega
                subst V
                exact q8_36
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q8_37
              · have he:V = 38:=by omega
                subst V
                exact q8_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q8_39
              · have he:V = 40:=by omega
                subst V
                exact q8_40
        · by_cases h41_50:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q8_41
              · have he:V = 42:=by omega
                subst V
                exact q8_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q8_43
              · have he:V = 44:=by omega
                subst V
                exact q8_44
          · by_cases h45_50:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q8_45
              · have he:V = 46:=by omega
                subst V
                exact q8_46
            · by_cases h47_50:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q8_47
              · by_cases h48_50:V < 49
                · have he:V = 48:=by omega
                  subst V
                  exact q8_48
                · have he:V = 49:=by omega
                  subst V
                  exact q8_49
      · by_cases h50_67:V < 58
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q8_50
              · have he:V = 51:=by omega
                subst V
                exact q8_51
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q8_52
              · have he:V = 53:=by omega
                subst V
                exact q8_53
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q8_54
              · have he:V = 55:=by omega
                subst V
                exact q8_55
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q8_56
              · have he:V = 57:=by omega
                subst V
                exact q8_57
        · by_cases h58_67:V < 62
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q8_58
              · have he:V = 59:=by omega
                subst V
                exact q8_59
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q8_60
              · have he:V = 61:=by omega
                subst V
                exact q8_61
          · by_cases h62_67:V < 64
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q8_62
              · have he:V = 63:=by omega
                subst V
                exact q8_63
            · by_cases h64_67:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q8_64
              · by_cases h65_67:V < 66
                · have he:V = 65:=by omega
                  subst V
                  exact q8_65
                · have he:V = 66:=by omega
                  subst V
                  exact q8_66
  · by_cases h67_135:V < 101
    · by_cases h67_101:V < 84
      · by_cases h67_84:V < 75
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q8_67
              · have he:V = 68:=by omega
                subst V
                exact q8_68
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q8_69
              · have he:V = 70:=by omega
                subst V
                exact q8_70
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q8_71
              · have he:V = 72:=by omega
                subst V
                exact q8_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q8_73
              · have he:V = 74:=by omega
                subst V
                exact q8_74
        · by_cases h75_84:V < 79
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q8_75
              · have he:V = 76:=by omega
                subst V
                exact q8_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q8_77
              · have he:V = 78:=by omega
                subst V
                exact q8_78
          · by_cases h79_84:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q8_79
              · have he:V = 80:=by omega
                subst V
                exact q8_80
            · by_cases h81_84:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q8_81
              · by_cases h82_84:V < 83
                · have he:V = 82:=by omega
                  subst V
                  exact q8_82
                · have he:V = 83:=by omega
                  subst V
                  exact q8_83
      · by_cases h84_101:V < 92
        · by_cases h84_92:V < 88
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q8_84
              · have he:V = 85:=by omega
                subst V
                exact q8_85
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q8_86
              · have he:V = 87:=by omega
                subst V
                exact q8_87
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q8_88
              · have he:V = 89:=by omega
                subst V
                exact q8_89
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q8_90
              · have he:V = 91:=by omega
                subst V
                exact q8_91
        · by_cases h92_101:V < 96
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q8_92
              · have he:V = 93:=by omega
                subst V
                exact q8_93
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q8_94
              · have he:V = 95:=by omega
                subst V
                exact q8_95
          · by_cases h96_101:V < 98
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q8_96
              · have he:V = 97:=by omega
                subst V
                exact q8_97
            · by_cases h98_101:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q8_98
              · by_cases h99_101:V < 100
                · have he:V = 99:=by omega
                  subst V
                  exact q8_99
                · have he:V = 100:=by omega
                  subst V
                  exact q8_100
    · by_cases h101_135:V < 118
      · by_cases h101_118:V < 109
        · by_cases h101_109:V < 105
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q8_101
              · have he:V = 102:=by omega
                subst V
                exact q8_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q8_103
              · have he:V = 104:=by omega
                subst V
                exact q8_104
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q8_105
              · have he:V = 106:=by omega
                subst V
                exact q8_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q8_107
              · have he:V = 108:=by omega
                subst V
                exact q8_108
        · by_cases h109_118:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q8_109
              · have he:V = 110:=by omega
                subst V
                exact q8_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q8_111
              · have he:V = 112:=by omega
                subst V
                exact q8_112
          · by_cases h113_118:V < 115
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q8_113
              · have he:V = 114:=by omega
                subst V
                exact q8_114
            · by_cases h115_118:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q8_115
              · by_cases h116_118:V < 117
                · have he:V = 116:=by omega
                  subst V
                  exact q8_116
                · have he:V = 117:=by omega
                  subst V
                  exact q8_117
      · by_cases h118_135:V < 126
        · by_cases h118_126:V < 122
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q8_118
              · have he:V = 119:=by omega
                subst V
                exact q8_119
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q8_120
              · have he:V = 121:=by omega
                subst V
                exact q8_121
          · by_cases h122_126:V < 124
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q8_122
              · have he:V = 123:=by omega
                subst V
                exact q8_123
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q8_124
              · have he:V = 125:=by omega
                subst V
                exact q8_125
        · by_cases h126_135:V < 130
          · by_cases h126_130:V < 128
            · by_cases h126_128:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q8_126
              · have he:V = 127:=by omega
                subst V
                exact q8_127
            · by_cases h128_130:V < 129
              · have he:V = 128:=by omega
                subst V
                exact q8_128
              · have he:V = 129:=by omega
                subst V
                exact q8_129
          · by_cases h130_135:V < 132
            · by_cases h130_132:V < 131
              · have he:V = 130:=by omega
                subst V
                exact q8_130
              · have he:V = 131:=by omega
                subst V
                exact q8_131
            · by_cases h132_135:V < 133
              · have he:V = 132:=by omega
                subst V
                exact q8_132
              · by_cases h133_135:V < 134
                · have he:V = 133:=by omega
                  subst V
                  exact q8_133
                · have he:V = 134:=by omega
                  subst V
                  exact q8_134
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
