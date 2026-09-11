import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked01

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q2_0:ThresholdAt 2 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 0 0 (by decide +kernel)
  | exact S 2 0 1 (by decide +kernel)
  | exact S 2 0 2 (by decide +kernel)
  | exact S 2 0 3 (by decide +kernel)
  | exact S 2 0 4 (by decide +kernel)
  | exact S 2 0 5 (by decide +kernel)
theorem q2_1:ThresholdAt 2 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 1 0 (by decide +kernel)
  | exact S 2 1 1 (by decide +kernel)
  | exact S 2 1 2 (by decide +kernel)
  | exact S 2 1 3 (by decide +kernel)
  | exact S 2 1 4 (by decide +kernel)
  | exact S 2 1 5 (by decide +kernel)
theorem q2_2:ThresholdAt 2 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 2 0 (by decide +kernel)
  | exact S 2 2 1 (by decide +kernel)
  | exact S 2 2 2 (by decide +kernel)
  | exact S 2 2 3 (by decide +kernel)
  | exact S 2 2 4 (by decide +kernel)
  | exact S 2 2 5 (by decide +kernel)
theorem q2_3:ThresholdAt 2 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 3 0 (by decide +kernel)
  | exact S 2 3 1 (by decide +kernel)
  | exact S 2 3 2 (by decide +kernel)
  | exact S 2 3 3 (by decide +kernel)
  | exact S 2 3 4 (by decide +kernel)
  | exact S 2 3 5 (by decide +kernel)
theorem q2_4:ThresholdAt 2 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 4 0 (by decide +kernel)
  | exact S 2 4 1 (by decide +kernel)
  | exact S 2 4 2 (by decide +kernel)
  | exact S 2 4 3 (by decide +kernel)
  | exact S 2 4 4 (by decide +kernel)
  | exact S 2 4 5 (by decide +kernel)
theorem q2_5:ThresholdAt 2 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 5 0 (by decide +kernel)
  | exact S 2 5 1 (by decide +kernel)
  | exact S 2 5 2 (by decide +kernel)
  | exact S 2 5 3 (by decide +kernel)
  | exact S 2 5 4 (by decide +kernel)
  | exact S 2 5 5 (by decide +kernel)
theorem q2_6:ThresholdAt 2 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 6 0 (by decide +kernel)
  | exact S 2 6 1 (by decide +kernel)
  | exact S 2 6 2 (by decide +kernel)
  | exact S 2 6 3 (by decide +kernel)
  | exact S 2 6 4 (by decide +kernel)
  | exact S 2 6 5 (by decide +kernel)
theorem q2_7:ThresholdAt 2 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 7 0 (by decide +kernel)
  | exact S 2 7 1 (by decide +kernel)
  | exact S 2 7 2 (by decide +kernel)
  | exact S 2 7 3 (by decide +kernel)
  | exact S 2 7 4 (by decide +kernel)
  | exact S 2 7 5 (by decide +kernel)
theorem q2_8:ThresholdAt 2 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 8 0 (by decide +kernel)
  | exact S 2 8 1 (by decide +kernel)
  | exact S 2 8 2 (by decide +kernel)
  | exact S 2 8 3 (by decide +kernel)
  | exact S 2 8 4 (by decide +kernel)
  | exact S 2 8 5 (by decide +kernel)
theorem q2_9:ThresholdAt 2 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 9 0 (by decide +kernel)
  | exact S 2 9 1 (by decide +kernel)
  | exact S 2 9 2 (by decide +kernel)
  | exact S 2 9 3 (by decide +kernel)
  | exact S 2 9 4 (by decide +kernel)
  | exact S 2 9 5 (by decide +kernel)
theorem q2_10:ThresholdAt 2 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 10 0 (by decide +kernel)
  | exact S 2 10 1 (by decide +kernel)
  | exact S 2 10 2 (by decide +kernel)
  | exact S 2 10 3 (by decide +kernel)
  | exact S 2 10 4 (by decide +kernel)
  | exact S 2 10 5 (by decide +kernel)
theorem q2_11:ThresholdAt 2 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 11 0 (by decide +kernel)
  | exact S 2 11 1 (by decide +kernel)
  | exact S 2 11 2 (by decide +kernel)
  | exact S 2 11 3 (by decide +kernel)
  | exact S 2 11 4 (by decide +kernel)
  | exact S 2 11 5 (by decide +kernel)
theorem q2_12:ThresholdAt 2 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 12 0 (by decide +kernel)
  | exact S 2 12 1 (by decide +kernel)
  | exact S 2 12 2 (by decide +kernel)
  | exact S 2 12 3 (by decide +kernel)
  | exact S 2 12 4 (by decide +kernel)
  | exact S 2 12 5 (by decide +kernel)
theorem q2_13:ThresholdAt 2 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 13 0 (by decide +kernel)
  | exact S 2 13 1 (by decide +kernel)
  | exact S 2 13 2 (by decide +kernel)
  | exact S 2 13 3 (by decide +kernel)
  | exact S 2 13 4 (by decide +kernel)
  | exact S 2 13 5 (by decide +kernel)
theorem q2_14:ThresholdAt 2 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 14 0 (by decide +kernel)
  | exact S 2 14 1 (by decide +kernel)
  | exact S 2 14 2 (by decide +kernel)
  | exact S 2 14 3 (by decide +kernel)
  | exact S 2 14 4 (by decide +kernel)
  | exact S 2 14 5 (by decide +kernel)
theorem q2_15:ThresholdAt 2 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 15 0 (by decide +kernel)
  | exact S 2 15 1 (by decide +kernel)
  | exact S 2 15 2 (by decide +kernel)
  | exact S 2 15 3 (by decide +kernel)
  | exact S 2 15 4 (by decide +kernel)
  | exact S 2 15 5 (by decide +kernel)
theorem q2_16:ThresholdAt 2 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 16 0 (by decide +kernel)
  | exact S 2 16 1 (by decide +kernel)
  | exact S 2 16 2 (by decide +kernel)
  | exact S 2 16 3 (by decide +kernel)
  | exact S 2 16 4 (by decide +kernel)
  | exact S 2 16 5 (by decide +kernel)
theorem q2_17:ThresholdAt 2 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 17 0 (by decide +kernel)
  | exact S 2 17 1 (by decide +kernel)
  | exact S 2 17 2 (by decide +kernel)
  | exact S 2 17 3 (by decide +kernel)
  | exact S 2 17 4 (by decide +kernel)
  | exact S 2 17 5 (by decide +kernel)
theorem q2_18:ThresholdAt 2 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 18 0 (by decide +kernel)
  | exact S 2 18 1 (by decide +kernel)
  | exact S 2 18 2 (by decide +kernel)
  | exact S 2 18 3 (by decide +kernel)
  | exact S 2 18 4 (by decide +kernel)
  | exact S 2 18 5 (by decide +kernel)
theorem q2_19:ThresholdAt 2 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 19 0 (by decide +kernel)
  | exact S 2 19 1 (by decide +kernel)
  | exact S 2 19 2 (by decide +kernel)
  | exact S 2 19 3 (by decide +kernel)
  | exact S 2 19 4 (by decide +kernel)
  | exact S 2 19 5 (by decide +kernel)
theorem q2_20:ThresholdAt 2 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 20 0 (by decide +kernel)
  | exact S 2 20 1 (by decide +kernel)
  | exact S 2 20 2 (by decide +kernel)
  | exact S 2 20 3 (by decide +kernel)
  | exact S 2 20 4 (by decide +kernel)
  | exact S 2 20 5 (by decide +kernel)
theorem q2_21:ThresholdAt 2 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 21 0 (by decide +kernel)
  | exact S 2 21 1 (by decide +kernel)
  | exact S 2 21 2 (by decide +kernel)
  | exact S 2 21 3 (by decide +kernel)
  | exact S 2 21 4 (by decide +kernel)
  | exact S 2 21 5 (by decide +kernel)
theorem q2_22:ThresholdAt 2 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 22 0 (by decide +kernel)
  | exact S 2 22 1 (by decide +kernel)
  | exact S 2 22 2 (by decide +kernel)
  | exact S 2 22 3 (by decide +kernel)
  | exact S 2 22 4 (by decide +kernel)
  | exact S 2 22 5 (by decide +kernel)
theorem q2_23:ThresholdAt 2 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 23 0 (by decide +kernel)
  | exact S 2 23 1 (by decide +kernel)
  | exact S 2 23 2 (by decide +kernel)
  | exact S 2 23 3 (by decide +kernel)
  | exact S 2 23 4 (by decide +kernel)
  | exact S 2 23 5 (by decide +kernel)
theorem q2_24:ThresholdAt 2 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 24 0 (by decide +kernel)
  | exact S 2 24 1 (by decide +kernel)
  | exact S 2 24 2 (by decide +kernel)
  | exact S 2 24 3 (by decide +kernel)
  | exact S 2 24 4 (by decide +kernel)
  | exact S 2 24 5 (by decide +kernel)
theorem q2_25:ThresholdAt 2 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 25 0 (by decide +kernel)
  | exact S 2 25 1 (by decide +kernel)
  | exact S 2 25 2 (by decide +kernel)
  | exact S 2 25 3 (by decide +kernel)
  | exact S 2 25 4 (by decide +kernel)
  | exact S 2 25 5 (by decide +kernel)
theorem q2_26:ThresholdAt 2 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 26 0 (by decide +kernel)
  | exact S 2 26 1 (by decide +kernel)
  | exact S 2 26 2 (by decide +kernel)
  | exact S 2 26 3 (by decide +kernel)
  | exact S 2 26 4 (by decide +kernel)
  | exact S 2 26 5 (by decide +kernel)
theorem q2_27:ThresholdAt 2 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 27 0 (by decide +kernel)
  | exact S 2 27 1 (by decide +kernel)
  | exact S 2 27 2 (by decide +kernel)
  | exact S 2 27 3 (by decide +kernel)
  | exact S 2 27 4 (by decide +kernel)
  | exact S 2 27 5 (by decide +kernel)
theorem q2_28:ThresholdAt 2 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 28 0 (by decide +kernel)
  | exact S 2 28 1 (by decide +kernel)
  | exact S 2 28 2 (by decide +kernel)
  | exact S 2 28 3 (by decide +kernel)
  | exact S 2 28 4 (by decide +kernel)
  | exact S 2 28 5 (by decide +kernel)
theorem q2_29:ThresholdAt 2 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 29 0 (by decide +kernel)
  | exact S 2 29 1 (by decide +kernel)
  | exact S 2 29 2 (by decide +kernel)
  | exact S 2 29 3 (by decide +kernel)
  | exact S 2 29 4 (by decide +kernel)
  | exact S 2 29 5 (by decide +kernel)
theorem q2_30:ThresholdAt 2 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 30 0 (by decide +kernel)
  | exact S 2 30 1 (by decide +kernel)
  | exact S 2 30 2 (by decide +kernel)
  | exact S 2 30 3 (by decide +kernel)
  | exact S 2 30 4 (by decide +kernel)
  | exact S 2 30 5 (by decide +kernel)
theorem q2_31:ThresholdAt 2 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 31 0 (by decide +kernel)
  | exact S 2 31 1 (by decide +kernel)
  | exact S 2 31 2 (by decide +kernel)
  | exact S 2 31 3 (by decide +kernel)
  | exact S 2 31 4 (by decide +kernel)
  | exact S 2 31 5 (by decide +kernel)
theorem q2_32:ThresholdAt 2 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 32 0 (by decide +kernel)
  | exact S 2 32 1 (by decide +kernel)
  | exact S 2 32 2 (by decide +kernel)
  | exact S 2 32 3 (by decide +kernel)
  | exact S 2 32 4 (by decide +kernel)
  | exact S 2 32 5 (by decide +kernel)
theorem q2_33:ThresholdAt 2 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 33 0 (by decide +kernel)
  | exact S 2 33 1 (by decide +kernel)
  | exact S 2 33 2 (by decide +kernel)
  | exact S 2 33 3 (by decide +kernel)
  | exact S 2 33 4 (by decide +kernel)
  | exact S 2 33 5 (by decide +kernel)
theorem q2_34:ThresholdAt 2 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 34 0 (by decide +kernel)
  | exact S 2 34 1 (by decide +kernel)
  | exact S 2 34 2 (by decide +kernel)
  | exact S 2 34 3 (by decide +kernel)
  | exact S 2 34 4 (by decide +kernel)
  | exact S 2 34 5 (by decide +kernel)
theorem q2_35:ThresholdAt 2 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 35 0 (by decide +kernel)
  | exact S 2 35 1 (by decide +kernel)
  | exact S 2 35 2 (by decide +kernel)
  | exact S 2 35 3 (by decide +kernel)
  | exact S 2 35 4 (by decide +kernel)
  | exact S 2 35 5 (by decide +kernel)
theorem q2_36:ThresholdAt 2 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 36 0 (by decide +kernel)
  | exact S 2 36 1 (by decide +kernel)
  | exact S 2 36 2 (by decide +kernel)
  | exact S 2 36 3 (by decide +kernel)
  | exact S 2 36 4 (by decide +kernel)
  | exact S 2 36 5 (by decide +kernel)
theorem q2_37:ThresholdAt 2 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 37 0 (by decide +kernel)
  | exact S 2 37 1 (by decide +kernel)
  | exact S 2 37 2 (by decide +kernel)
  | exact S 2 37 3 (by decide +kernel)
  | exact S 2 37 4 (by decide +kernel)
  | exact S 2 37 5 (by decide +kernel)
theorem q2_38:ThresholdAt 2 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 38 0 (by decide +kernel)
  | exact S 2 38 1 (by decide +kernel)
  | exact S 2 38 2 (by decide +kernel)
  | exact S 2 38 3 (by decide +kernel)
  | exact S 2 38 4 (by decide +kernel)
  | exact S 2 38 5 (by decide +kernel)
theorem q2_39:ThresholdAt 2 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 39 0 (by decide +kernel)
  | exact S 2 39 1 (by decide +kernel)
  | exact S 2 39 2 (by decide +kernel)
  | exact S 2 39 3 (by decide +kernel)
  | exact S 2 39 4 (by decide +kernel)
  | exact S 2 39 5 (by decide +kernel)
theorem q2_40:ThresholdAt 2 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 40 0 (by decide +kernel)
  | exact S 2 40 1 (by decide +kernel)
  | exact S 2 40 2 (by decide +kernel)
  | exact S 2 40 3 (by decide +kernel)
  | exact S 2 40 4 (by decide +kernel)
  | exact S 2 40 5 (by decide +kernel)
theorem q2_41:ThresholdAt 2 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 41 0 (by decide +kernel)
  | exact S 2 41 1 (by decide +kernel)
  | exact S 2 41 2 (by decide +kernel)
  | exact S 2 41 3 (by decide +kernel)
  | exact S 2 41 4 (by decide +kernel)
  | exact S 2 41 5 (by decide +kernel)
theorem q2_42:ThresholdAt 2 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 42 0 (by decide +kernel)
  | exact S 2 42 1 (by decide +kernel)
  | exact S 2 42 2 (by decide +kernel)
  | exact S 2 42 3 (by decide +kernel)
  | exact S 2 42 4 (by decide +kernel)
  | exact S 2 42 5 (by decide +kernel)
theorem q2_43:ThresholdAt 2 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 43 0 (by decide +kernel)
  | exact S 2 43 1 (by decide +kernel)
  | exact S 2 43 2 (by decide +kernel)
  | exact S 2 43 3 (by decide +kernel)
  | exact S 2 43 4 (by decide +kernel)
  | exact S 2 43 5 (by decide +kernel)
theorem q2_44:ThresholdAt 2 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 44 0 (by decide +kernel)
  | exact S 2 44 1 (by decide +kernel)
  | exact S 2 44 2 (by decide +kernel)
  | exact S 2 44 3 (by decide +kernel)
  | exact S 2 44 4 (by decide +kernel)
  | exact S 2 44 5 (by decide +kernel)
theorem q2_45:ThresholdAt 2 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 45 0 (by decide +kernel)
  | exact S 2 45 1 (by decide +kernel)
  | exact S 2 45 2 (by decide +kernel)
  | exact S 2 45 3 (by decide +kernel)
  | exact S 2 45 4 (by decide +kernel)
  | exact S 2 45 5 (by decide +kernel)
theorem q2_46:ThresholdAt 2 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 46 0 (by decide +kernel)
  | exact S 2 46 1 (by decide +kernel)
  | exact S 2 46 2 (by decide +kernel)
  | exact S 2 46 3 (by decide +kernel)
  | exact S 2 46 4 (by decide +kernel)
  | exact S 2 46 5 (by decide +kernel)
theorem q2_47:ThresholdAt 2 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 47 0 (by decide +kernel)
  | exact S 2 47 1 (by decide +kernel)
  | exact S 2 47 2 (by decide +kernel)
  | exact S 2 47 3 (by decide +kernel)
  | exact S 2 47 4 (by decide +kernel)
  | exact S 2 47 5 (by decide +kernel)
theorem q2_48:ThresholdAt 2 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 48 0 (by decide +kernel)
  | exact S 2 48 1 (by decide +kernel)
  | exact S 2 48 2 (by decide +kernel)
  | exact S 2 48 3 (by decide +kernel)
  | exact S 2 48 4 (by decide +kernel)
  | exact S 2 48 5 (by decide +kernel)
theorem q2_49:ThresholdAt 2 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 49 0 (by decide +kernel)
  | exact S 2 49 1 (by decide +kernel)
  | exact S 2 49 2 (by decide +kernel)
  | exact S 2 49 3 (by decide +kernel)
  | exact S 2 49 4 (by decide +kernel)
  | exact S 2 49 5 (by decide +kernel)
theorem q2_50:ThresholdAt 2 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 50 0 (by decide +kernel)
  | exact S 2 50 1 (by decide +kernel)
  | exact S 2 50 2 (by decide +kernel)
  | exact S 2 50 3 (by decide +kernel)
  | exact S 2 50 4 (by decide +kernel)
  | exact S 2 50 5 (by decide +kernel)
theorem q2_51:ThresholdAt 2 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 51 0 (by decide +kernel)
  | exact S 2 51 1 (by decide +kernel)
  | exact S 2 51 2 (by decide +kernel)
  | exact S 2 51 3 (by decide +kernel)
  | exact S 2 51 4 (by decide +kernel)
  | exact S 2 51 5 (by decide +kernel)
theorem q2_52:ThresholdAt 2 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 52 0 (by decide +kernel)
  | exact S 2 52 1 (by decide +kernel)
  | exact S 2 52 2 (by decide +kernel)
  | exact S 2 52 3 (by decide +kernel)
  | exact S 2 52 4 (by decide +kernel)
  | exact S 2 52 5 (by decide +kernel)
theorem q2_53:ThresholdAt 2 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 53 0 (by decide +kernel)
  | exact S 2 53 1 (by decide +kernel)
  | exact S 2 53 2 (by decide +kernel)
  | exact S 2 53 3 (by decide +kernel)
  | exact S 2 53 4 (by decide +kernel)
  | exact S 2 53 5 (by decide +kernel)
theorem q2_54:ThresholdAt 2 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 54 0 (by decide +kernel)
  | exact S 2 54 1 (by decide +kernel)
  | exact S 2 54 2 (by decide +kernel)
  | exact S 2 54 3 (by decide +kernel)
  | exact S 2 54 4 (by decide +kernel)
  | exact S 2 54 5 (by decide +kernel)
theorem q2_55:ThresholdAt 2 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 55 0 (by decide +kernel)
  | exact S 2 55 1 (by decide +kernel)
  | exact S 2 55 2 (by decide +kernel)
  | exact S 2 55 3 (by decide +kernel)
  | exact S 2 55 4 (by decide +kernel)
  | exact S 2 55 5 (by decide +kernel)
theorem q2_56:ThresholdAt 2 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 56 0 (by decide +kernel)
  | exact S 2 56 1 (by decide +kernel)
  | exact S 2 56 2 (by decide +kernel)
  | exact S 2 56 3 (by decide +kernel)
  | exact S 2 56 4 (by decide +kernel)
  | exact S 2 56 5 (by decide +kernel)
theorem q2_57:ThresholdAt 2 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 57 0 (by decide +kernel)
  | exact S 2 57 1 (by decide +kernel)
  | exact S 2 57 2 (by decide +kernel)
  | exact S 2 57 3 (by decide +kernel)
  | exact S 2 57 4 (by decide +kernel)
  | exact S 2 57 5 (by decide +kernel)
theorem q2_58:ThresholdAt 2 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 58 0 (by decide +kernel)
  | exact S 2 58 1 (by decide +kernel)
  | exact S 2 58 2 (by decide +kernel)
  | exact S 2 58 3 (by decide +kernel)
  | exact S 2 58 4 (by decide +kernel)
  | exact S 2 58 5 (by decide +kernel)
theorem q2_59:ThresholdAt 2 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 59 0 (by decide +kernel)
  | exact S 2 59 1 (by decide +kernel)
  | exact S 2 59 2 (by decide +kernel)
  | exact S 2 59 3 (by decide +kernel)
  | exact S 2 59 4 (by decide +kernel)
  | exact S 2 59 5 (by decide +kernel)
theorem q2_60:ThresholdAt 2 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 60 0 (by decide +kernel)
  | exact S 2 60 1 (by decide +kernel)
  | exact S 2 60 2 (by decide +kernel)
  | exact S 2 60 3 (by decide +kernel)
  | exact S 2 60 4 (by decide +kernel)
  | exact S 2 60 5 (by decide +kernel)
theorem q2_61:ThresholdAt 2 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 61 0 (by decide +kernel)
  | exact S 2 61 1 (by decide +kernel)
  | exact S 2 61 2 (by decide +kernel)
  | exact S 2 61 3 (by decide +kernel)
  | exact S 2 61 4 (by decide +kernel)
  | exact S 2 61 5 (by decide +kernel)
theorem q2_62:ThresholdAt 2 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 62 0 (by decide +kernel)
  | exact S 2 62 1 (by decide +kernel)
  | exact S 2 62 2 (by decide +kernel)
  | exact S 2 62 3 (by decide +kernel)
  | exact S 2 62 4 (by decide +kernel)
  | exact S 2 62 5 (by decide +kernel)
theorem q2_63:ThresholdAt 2 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 63 0 (by decide +kernel)
  | exact S 2 63 1 (by decide +kernel)
  | exact S 2 63 2 (by decide +kernel)
  | exact S 2 63 3 (by decide +kernel)
  | exact S 2 63 4 (by decide +kernel)
  | exact S 2 63 5 (by decide +kernel)
theorem q2_64:ThresholdAt 2 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 64 0 (by decide +kernel)
  | exact S 2 64 1 (by decide +kernel)
  | exact S 2 64 2 (by decide +kernel)
  | exact S 2 64 3 (by decide +kernel)
  | exact S 2 64 4 (by decide +kernel)
  | exact S 2 64 5 (by decide +kernel)
theorem q2_65:ThresholdAt 2 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 65 0 (by decide +kernel)
  | exact S 2 65 1 (by decide +kernel)
  | exact S 2 65 2 (by decide +kernel)
  | exact S 2 65 3 (by decide +kernel)
  | exact S 2 65 4 (by decide +kernel)
  | exact S 2 65 5 (by decide +kernel)
theorem q2_66:ThresholdAt 2 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 66 0 (by decide +kernel)
  | exact S 2 66 1 (by decide +kernel)
  | exact S 2 66 2 (by decide +kernel)
  | exact S 2 66 3 (by decide +kernel)
  | exact S 2 66 4 (by decide +kernel)
  | exact S 2 66 5 (by decide +kernel)
theorem q2_67:ThresholdAt 2 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 67 0 (by decide +kernel)
  | exact S 2 67 1 (by decide +kernel)
  | exact S 2 67 2 (by decide +kernel)
  | exact S 2 67 3 (by decide +kernel)
  | exact S 2 67 4 (by decide +kernel)
  | exact S 2 67 5 (by decide +kernel)
theorem q2_68:ThresholdAt 2 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 68 0 (by decide +kernel)
  | exact S 2 68 1 (by decide +kernel)
  | exact S 2 68 2 (by decide +kernel)
  | exact S 2 68 3 (by decide +kernel)
  | exact S 2 68 4 (by decide +kernel)
  | exact S 2 68 5 (by decide +kernel)
theorem q2_69:ThresholdAt 2 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 69 0 (by decide +kernel)
  | exact S 2 69 1 (by decide +kernel)
  | exact S 2 69 2 (by decide +kernel)
  | exact S 2 69 3 (by decide +kernel)
  | exact S 2 69 4 (by decide +kernel)
  | exact S 2 69 5 (by decide +kernel)
theorem q2_70:ThresholdAt 2 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 70 0 (by decide +kernel)
  | exact S 2 70 1 (by decide +kernel)
  | exact S 2 70 2 (by decide +kernel)
  | exact S 2 70 3 (by decide +kernel)
  | exact S 2 70 4 (by decide +kernel)
  | exact S 2 70 5 (by decide +kernel)
theorem q2_71:ThresholdAt 2 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 71 0 (by decide +kernel)
  | exact S 2 71 1 (by decide +kernel)
  | exact S 2 71 2 (by decide +kernel)
  | exact S 2 71 3 (by decide +kernel)
  | exact S 2 71 4 (by decide +kernel)
  | exact S 2 71 5 (by decide +kernel)
theorem q2_72:ThresholdAt 2 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 72 0 (by decide +kernel)
  | exact S 2 72 1 (by decide +kernel)
  | exact S 2 72 2 (by decide +kernel)
  | exact S 2 72 3 (by decide +kernel)
  | exact S 2 72 4 (by decide +kernel)
  | exact S 2 72 5 (by decide +kernel)
theorem q2_73:ThresholdAt 2 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 73 0 (by decide +kernel)
  | exact S 2 73 1 (by decide +kernel)
  | exact S 2 73 2 (by decide +kernel)
  | exact S 2 73 3 (by decide +kernel)
  | exact S 2 73 4 (by decide +kernel)
  | exact S 2 73 5 (by decide +kernel)
theorem q2_74:ThresholdAt 2 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 74 0 (by decide +kernel)
  | exact S 2 74 1 (by decide +kernel)
  | exact S 2 74 2 (by decide +kernel)
  | exact S 2 74 3 (by decide +kernel)
  | exact S 2 74 4 (by decide +kernel)
  | exact S 2 74 5 (by decide +kernel)
theorem q2_75:ThresholdAt 2 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 75 0 (by decide +kernel)
  | exact S 2 75 1 (by decide +kernel)
  | exact S 2 75 2 (by decide +kernel)
  | exact S 2 75 3 (by decide +kernel)
  | exact S 2 75 4 (by decide +kernel)
  | exact S 2 75 5 (by decide +kernel)
theorem q2_76:ThresholdAt 2 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 76 0 (by decide +kernel)
  | exact S 2 76 1 (by decide +kernel)
  | exact S 2 76 2 (by decide +kernel)
  | exact S 2 76 3 (by decide +kernel)
  | exact S 2 76 4 (by decide +kernel)
  | exact S 2 76 5 (by decide +kernel)
theorem q2_77:ThresholdAt 2 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 77 0 (by decide +kernel)
  | exact S 2 77 1 (by decide +kernel)
  | exact S 2 77 2 (by decide +kernel)
  | exact S 2 77 3 (by decide +kernel)
  | exact S 2 77 4 (by decide +kernel)
  | exact S 2 77 5 (by decide +kernel)
theorem q2_78:ThresholdAt 2 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 78 0 (by decide +kernel)
  | exact S 2 78 1 (by decide +kernel)
  | exact S 2 78 2 (by decide +kernel)
  | exact S 2 78 3 (by decide +kernel)
  | exact S 2 78 4 (by decide +kernel)
  | exact S 2 78 5 (by decide +kernel)
theorem q2_79:ThresholdAt 2 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 79 0 (by decide +kernel)
  | exact S 2 79 1 (by decide +kernel)
  | exact S 2 79 2 (by decide +kernel)
  | exact S 2 79 3 (by decide +kernel)
  | exact S 2 79 4 (by decide +kernel)
  | exact S 2 79 5 (by decide +kernel)
theorem q2_80:ThresholdAt 2 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 80 0 (by decide +kernel)
  | exact S 2 80 1 (by decide +kernel)
  | exact S 2 80 2 (by decide +kernel)
  | exact S 2 80 3 (by decide +kernel)
  | exact S 2 80 4 (by decide +kernel)
  | exact S 2 80 5 (by decide +kernel)
theorem q2_81:ThresholdAt 2 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 81 0 (by decide +kernel)
  | exact S 2 81 1 (by decide +kernel)
  | exact S 2 81 2 (by decide +kernel)
  | exact S 2 81 3 (by decide +kernel)
  | exact S 2 81 4 (by decide +kernel)
  | exact S 2 81 5 (by decide +kernel)
theorem q2_82:ThresholdAt 2 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 82 0 (by decide +kernel)
  | exact S 2 82 1 (by decide +kernel)
  | exact S 2 82 2 (by decide +kernel)
  | exact S 2 82 3 (by decide +kernel)
  | exact S 2 82 4 (by decide +kernel)
  | exact S 2 82 5 (by decide +kernel)
theorem q2_83:ThresholdAt 2 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 83 0 (by decide +kernel)
  | exact S 2 83 1 (by decide +kernel)
  | exact S 2 83 2 (by decide +kernel)
  | exact S 2 83 3 (by decide +kernel)
  | exact S 2 83 4 (by decide +kernel)
  | exact S 2 83 5 (by decide +kernel)
theorem q2_84:ThresholdAt 2 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 84 0 (by decide +kernel)
  | exact S 2 84 1 (by decide +kernel)
  | exact S 2 84 2 (by decide +kernel)
  | exact S 2 84 3 (by decide +kernel)
  | exact S 2 84 4 (by decide +kernel)
  | exact S 2 84 5 (by decide +kernel)
theorem q2_85:ThresholdAt 2 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 85 0 (by decide +kernel)
  | exact S 2 85 1 (by decide +kernel)
  | exact S 2 85 2 (by decide +kernel)
  | exact S 2 85 3 (by decide +kernel)
  | exact S 2 85 4 (by decide +kernel)
  | exact S 2 85 5 (by decide +kernel)
theorem q2_86:ThresholdAt 2 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 86 0 (by decide +kernel)
  | exact S 2 86 1 (by decide +kernel)
  | exact S 2 86 2 (by decide +kernel)
  | exact S 2 86 3 (by decide +kernel)
  | exact S 2 86 4 (by decide +kernel)
  | exact S 2 86 5 (by decide +kernel)
theorem q2_87:ThresholdAt 2 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 87 0 (by decide +kernel)
  | exact S 2 87 1 (by decide +kernel)
  | exact S 2 87 2 (by decide +kernel)
  | exact S 2 87 3 (by decide +kernel)
  | exact S 2 87 4 (by decide +kernel)
  | exact S 2 87 5 (by decide +kernel)
theorem q2_88:ThresholdAt 2 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 88 0 (by decide +kernel)
  | exact S 2 88 1 (by decide +kernel)
  | exact S 2 88 2 (by decide +kernel)
  | exact S 2 88 3 (by decide +kernel)
  | exact S 2 88 4 (by decide +kernel)
  | exact S 2 88 5 (by decide +kernel)
theorem q2_89:ThresholdAt 2 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 89 0 (by decide +kernel)
  | exact S 2 89 1 (by decide +kernel)
  | exact S 2 89 2 (by decide +kernel)
  | exact S 2 89 3 (by decide +kernel)
  | exact S 2 89 4 (by decide +kernel)
  | exact S 2 89 5 (by decide +kernel)
theorem q2_90:ThresholdAt 2 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 90 0 (by decide +kernel)
  | exact S 2 90 1 (by decide +kernel)
  | exact S 2 90 2 (by decide +kernel)
  | exact S 2 90 3 (by decide +kernel)
  | exact S 2 90 4 (by decide +kernel)
  | exact S 2 90 5 (by decide +kernel)
theorem q2_91:ThresholdAt 2 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 91 0 (by decide +kernel)
  | exact S 2 91 1 (by decide +kernel)
  | exact S 2 91 2 (by decide +kernel)
  | exact S 2 91 3 (by decide +kernel)
  | exact S 2 91 4 (by decide +kernel)
  | exact S 2 91 5 (by decide +kernel)
theorem q2_92:ThresholdAt 2 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 92 0 (by decide +kernel)
  | exact S 2 92 1 (by decide +kernel)
  | exact S 2 92 2 (by decide +kernel)
  | exact S 2 92 3 (by decide +kernel)
  | exact S 2 92 4 (by decide +kernel)
  | exact S 2 92 5 (by decide +kernel)
theorem q2_93:ThresholdAt 2 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 93 0 (by decide +kernel)
  | exact S 2 93 1 (by decide +kernel)
  | exact S 2 93 2 (by decide +kernel)
  | exact S 2 93 3 (by decide +kernel)
  | exact S 2 93 4 (by decide +kernel)
  | exact S 2 93 5 (by decide +kernel)
theorem q2_94:ThresholdAt 2 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 94 0 (by decide +kernel)
  | exact S 2 94 1 (by decide +kernel)
  | exact S 2 94 2 (by decide +kernel)
  | exact S 2 94 3 (by decide +kernel)
  | exact S 2 94 4 (by decide +kernel)
  | exact S 2 94 5 (by decide +kernel)
theorem q2_95:ThresholdAt 2 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 95 0 (by decide +kernel)
  | exact S 2 95 1 (by decide +kernel)
  | exact S 2 95 2 (by decide +kernel)
  | exact S 2 95 3 (by decide +kernel)
  | exact S 2 95 4 (by decide +kernel)
  | exact S 2 95 5 (by decide +kernel)
theorem q2_96:ThresholdAt 2 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 96 0 (by decide +kernel)
  | exact S 2 96 1 (by decide +kernel)
  | exact S 2 96 2 (by decide +kernel)
  | exact S 2 96 3 (by decide +kernel)
  | exact S 2 96 4 (by decide +kernel)
  | exact S 2 96 5 (by decide +kernel)
theorem q2_97:ThresholdAt 2 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 97 0 (by decide +kernel)
  | exact S 2 97 1 (by decide +kernel)
  | exact S 2 97 2 (by decide +kernel)
  | exact S 2 97 3 (by decide +kernel)
  | exact S 2 97 4 (by decide +kernel)
  | exact S 2 97 5 (by decide +kernel)
theorem q2_98:ThresholdAt 2 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 98 0 (by decide +kernel)
  | exact S 2 98 1 (by decide +kernel)
  | exact S 2 98 2 (by decide +kernel)
  | exact S 2 98 3 (by decide +kernel)
  | exact S 2 98 4 (by decide +kernel)
  | exact S 2 98 5 (by decide +kernel)
theorem q2_99:ThresholdAt 2 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 99 0 (by decide +kernel)
  | exact S 2 99 1 (by decide +kernel)
  | exact S 2 99 2 (by decide +kernel)
  | exact S 2 99 3 (by decide +kernel)
  | exact S 2 99 4 (by decide +kernel)
  | exact S 2 99 5 (by decide +kernel)
theorem q2_100:ThresholdAt 2 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 100 0 (by decide +kernel)
  | exact S 2 100 1 (by decide +kernel)
  | exact S 2 100 2 (by decide +kernel)
  | exact S 2 100 3 (by decide +kernel)
  | exact S 2 100 4 (by decide +kernel)
  | exact S 2 100 5 (by decide +kernel)
theorem q2_101:ThresholdAt 2 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 101 0 (by decide +kernel)
  | exact S 2 101 1 (by decide +kernel)
  | exact S 2 101 2 (by decide +kernel)
  | exact S 2 101 3 (by decide +kernel)
  | exact S 2 101 4 (by decide +kernel)
  | exact S 2 101 5 (by decide +kernel)
theorem q2_102:ThresholdAt 2 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 102 0 (by decide +kernel)
  | exact S 2 102 1 (by decide +kernel)
  | exact S 2 102 2 (by decide +kernel)
  | exact S 2 102 3 (by decide +kernel)
  | exact S 2 102 4 (by decide +kernel)
  | exact S 2 102 5 (by decide +kernel)
theorem q2_103:ThresholdAt 2 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 103 0 (by decide +kernel)
  | exact S 2 103 1 (by decide +kernel)
  | exact S 2 103 2 (by decide +kernel)
  | exact S 2 103 3 (by decide +kernel)
  | exact S 2 103 4 (by decide +kernel)
  | exact S 2 103 5 (by decide +kernel)
theorem q2_104:ThresholdAt 2 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 104 0 (by decide +kernel)
  | exact S 2 104 1 (by decide +kernel)
  | exact S 2 104 2 (by decide +kernel)
  | exact S 2 104 3 (by decide +kernel)
  | exact S 2 104 4 (by decide +kernel)
  | exact S 2 104 5 (by decide +kernel)
theorem q2_105:ThresholdAt 2 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 105 0 (by decide +kernel)
  | exact S 2 105 1 (by decide +kernel)
  | exact S 2 105 2 (by decide +kernel)
  | exact S 2 105 3 (by decide +kernel)
  | exact S 2 105 4 (by decide +kernel)
  | exact S 2 105 5 (by decide +kernel)
theorem q2_106:ThresholdAt 2 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 106 0 (by decide +kernel)
  | exact S 2 106 1 (by decide +kernel)
  | exact S 2 106 2 (by decide +kernel)
  | exact S 2 106 3 (by decide +kernel)
  | exact S 2 106 4 (by decide +kernel)
  | exact S 2 106 5 (by decide +kernel)
theorem q2_107:ThresholdAt 2 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 107 0 (by decide +kernel)
  | exact S 2 107 1 (by decide +kernel)
  | exact S 2 107 2 (by decide +kernel)
  | exact S 2 107 3 (by decide +kernel)
  | exact S 2 107 4 (by decide +kernel)
  | exact S 2 107 5 (by decide +kernel)
theorem q2_108:ThresholdAt 2 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 108 0 (by decide +kernel)
  | exact S 2 108 1 (by decide +kernel)
  | exact S 2 108 2 (by decide +kernel)
  | exact S 2 108 3 (by decide +kernel)
  | exact S 2 108 4 (by decide +kernel)
  | exact S 2 108 5 (by decide +kernel)
theorem q2_109:ThresholdAt 2 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 109 0 (by decide +kernel)
  | exact S 2 109 1 (by decide +kernel)
  | exact S 2 109 2 (by decide +kernel)
  | exact S 2 109 3 (by decide +kernel)
  | exact S 2 109 4 (by decide +kernel)
  | exact S 2 109 5 (by decide +kernel)
theorem q2_110:ThresholdAt 2 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 110 0 (by decide +kernel)
  | exact S 2 110 1 (by decide +kernel)
  | exact S 2 110 2 (by decide +kernel)
  | exact S 2 110 3 (by decide +kernel)
  | exact S 2 110 4 (by decide +kernel)
  | exact S 2 110 5 (by decide +kernel)
theorem q2_111:ThresholdAt 2 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 111 0 (by decide +kernel)
  | exact S 2 111 1 (by decide +kernel)
  | exact S 2 111 2 (by decide +kernel)
  | exact S 2 111 3 (by decide +kernel)
  | exact S 2 111 4 (by decide +kernel)
  | exact S 2 111 5 (by decide +kernel)
theorem q2_112:ThresholdAt 2 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 112 0 (by decide +kernel)
  | exact S 2 112 1 (by decide +kernel)
  | exact S 2 112 2 (by decide +kernel)
  | exact S 2 112 3 (by decide +kernel)
  | exact S 2 112 4 (by decide +kernel)
  | exact S 2 112 5 (by decide +kernel)
theorem q2_113:ThresholdAt 2 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 113 0 (by decide +kernel)
  | exact S 2 113 1 (by decide +kernel)
  | exact S 2 113 2 (by decide +kernel)
  | exact S 2 113 3 (by decide +kernel)
  | exact S 2 113 4 (by decide +kernel)
  | exact S 2 113 5 (by decide +kernel)
theorem q2_114:ThresholdAt 2 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 114 0 (by decide +kernel)
  | exact S 2 114 1 (by decide +kernel)
  | exact S 2 114 2 (by decide +kernel)
  | exact S 2 114 3 (by decide +kernel)
  | exact S 2 114 4 (by decide +kernel)
  | exact S 2 114 5 (by decide +kernel)
theorem q2_115:ThresholdAt 2 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 115 0 (by decide +kernel)
  | exact S 2 115 1 (by decide +kernel)
  | exact S 2 115 2 (by decide +kernel)
  | exact S 2 115 3 (by decide +kernel)
  | exact S 2 115 4 (by decide +kernel)
  | exact S 2 115 5 (by decide +kernel)
theorem q2_116:ThresholdAt 2 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 116 0 (by decide +kernel)
  | exact S 2 116 1 (by decide +kernel)
  | exact S 2 116 2 (by decide +kernel)
  | exact S 2 116 3 (by decide +kernel)
  | exact S 2 116 4 (by decide +kernel)
  | exact S 2 116 5 (by decide +kernel)
theorem q2_117:ThresholdAt 2 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 117 0 (by decide +kernel)
  | exact S 2 117 1 (by decide +kernel)
  | exact S 2 117 2 (by decide +kernel)
  | exact S 2 117 3 (by decide +kernel)
  | exact S 2 117 4 (by decide +kernel)
  | exact S 2 117 5 (by decide +kernel)
theorem q2_118:ThresholdAt 2 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 118 0 (by decide +kernel)
  | exact S 2 118 1 (by decide +kernel)
  | exact S 2 118 2 (by decide +kernel)
  | exact S 2 118 3 (by decide +kernel)
  | exact S 2 118 4 (by decide +kernel)
  | exact S 2 118 5 (by decide +kernel)
theorem q2_119:ThresholdAt 2 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 119 0 (by decide +kernel)
  | exact S 2 119 1 (by decide +kernel)
  | exact S 2 119 2 (by decide +kernel)
  | exact S 2 119 3 (by decide +kernel)
  | exact S 2 119 4 (by decide +kernel)
  | exact S 2 119 5 (by decide +kernel)
theorem q2_120:ThresholdAt 2 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 120 0 (by decide +kernel)
  | exact S 2 120 1 (by decide +kernel)
  | exact S 2 120 2 (by decide +kernel)
  | exact S 2 120 3 (by decide +kernel)
  | exact S 2 120 4 (by decide +kernel)
  | exact S 2 120 5 (by decide +kernel)
theorem q2_121:ThresholdAt 2 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 121 0 (by decide +kernel)
  | exact S 2 121 1 (by decide +kernel)
  | exact S 2 121 2 (by decide +kernel)
  | exact S 2 121 3 (by decide +kernel)
  | exact S 2 121 4 (by decide +kernel)
  | exact S 2 121 5 (by decide +kernel)
theorem q2_122:ThresholdAt 2 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 122 0 (by decide +kernel)
  | exact S 2 122 1 (by decide +kernel)
  | exact S 2 122 2 (by decide +kernel)
  | exact S 2 122 3 (by decide +kernel)
  | exact S 2 122 4 (by decide +kernel)
  | exact S 2 122 5 (by decide +kernel)
theorem q2_123:ThresholdAt 2 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 123 0 (by decide +kernel)
  | exact S 2 123 1 (by decide +kernel)
  | exact S 2 123 2 (by decide +kernel)
  | exact S 2 123 3 (by decide +kernel)
  | exact S 2 123 4 (by decide +kernel)
  | exact S 2 123 5 (by decide +kernel)
theorem q2_124:ThresholdAt 2 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 124 0 (by decide +kernel)
  | exact S 2 124 1 (by decide +kernel)
  | exact S 2 124 2 (by decide +kernel)
  | exact S 2 124 3 (by decide +kernel)
  | exact S 2 124 4 (by decide +kernel)
  | exact S 2 124 5 (by decide +kernel)
theorem q2_125:ThresholdAt 2 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 125 0 (by decide +kernel)
  | exact S 2 125 1 (by decide +kernel)
  | exact S 2 125 2 (by decide +kernel)
  | exact S 2 125 3 (by decide +kernel)
  | exact S 2 125 4 (by decide +kernel)
  | exact S 2 125 5 (by decide +kernel)
theorem q2_126:ThresholdAt 2 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 126 0 (by decide +kernel)
  | exact S 2 126 1 (by decide +kernel)
  | exact S 2 126 2 (by decide +kernel)
  | exact S 2 126 3 (by decide +kernel)
  | exact S 2 126 4 (by decide +kernel)
  | exact S 2 126 5 (by decide +kernel)
theorem q2_127:ThresholdAt 2 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 127 0 (by decide +kernel)
  | exact S 2 127 1 (by decide +kernel)
  | exact S 2 127 2 (by decide +kernel)
  | exact S 2 127 3 (by decide +kernel)
  | exact S 2 127 4 (by decide +kernel)
  | exact S 2 127 5 (by decide +kernel)
theorem q2_128:ThresholdAt 2 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 128 0 (by decide +kernel)
  | exact S 2 128 1 (by decide +kernel)
  | exact S 2 128 2 (by decide +kernel)
  | exact S 2 128 3 (by decide +kernel)
  | exact S 2 128 4 (by decide +kernel)
  | exact S 2 128 5 (by decide +kernel)
theorem q2_129:ThresholdAt 2 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 129 0 (by decide +kernel)
  | exact S 2 129 1 (by decide +kernel)
  | exact S 2 129 2 (by decide +kernel)
  | exact S 2 129 3 (by decide +kernel)
  | exact S 2 129 4 (by decide +kernel)
  | exact S 2 129 5 (by decide +kernel)
theorem q2_130:ThresholdAt 2 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 130 0 (by decide +kernel)
  | exact S 2 130 1 (by decide +kernel)
  | exact S 2 130 2 (by decide +kernel)
  | exact S 2 130 3 (by decide +kernel)
  | exact S 2 130 4 (by decide +kernel)
  | exact S 2 130 5 (by decide +kernel)
theorem q2_131:ThresholdAt 2 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 131 0 (by decide +kernel)
  | exact S 2 131 1 (by decide +kernel)
  | exact S 2 131 2 (by decide +kernel)
  | exact S 2 131 3 (by decide +kernel)
  | exact S 2 131 4 (by decide +kernel)
  | exact S 2 131 5 (by decide +kernel)
theorem q2_132:ThresholdAt 2 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 132 0 (by decide +kernel)
  | exact S 2 132 1 (by decide +kernel)
  | exact S 2 132 2 (by decide +kernel)
  | exact S 2 132 3 (by decide +kernel)
  | exact S 2 132 4 (by decide +kernel)
  | exact S 2 132 5 (by decide +kernel)
theorem q2_133:ThresholdAt 2 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 133 0 (by decide +kernel)
  | exact S 2 133 1 (by decide +kernel)
  | exact S 2 133 2 (by decide +kernel)
  | exact S 2 133 3 (by decide +kernel)
  | exact S 2 133 4 (by decide +kernel)
  | exact S 2 133 5 (by decide +kernel)
theorem q2_134:ThresholdAt 2 134:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 134 0 (by decide +kernel)
  | exact S 2 134 1 (by decide +kernel)
  | exact S 2 134 2 (by decide +kernel)
  | exact S 2 134 3 (by decide +kernel)
  | exact S 2 134 4 (by decide +kernel)
  | exact S 2 134 5 (by decide +kernel)
theorem q2_135:ThresholdAt 2 135:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 135 0 (by decide +kernel)
  | exact S 2 135 1 (by decide +kernel)
  | exact S 2 135 2 (by decide +kernel)
  | exact S 2 135 3 (by decide +kernel)
  | exact S 2 135 4 (by decide +kernel)
  | exact S 2 135 5 (by decide +kernel)
theorem q2_136:ThresholdAt 2 136:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 136 0 (by decide +kernel)
  | exact S 2 136 1 (by decide +kernel)
  | exact S 2 136 2 (by decide +kernel)
  | exact S 2 136 3 (by decide +kernel)
  | exact S 2 136 4 (by decide +kernel)
  | exact S 2 136 5 (by decide +kernel)
theorem q2_137:ThresholdAt 2 137:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 137 0 (by decide +kernel)
  | exact S 2 137 1 (by decide +kernel)
  | exact S 2 137 2 (by decide +kernel)
  | exact S 2 137 3 (by decide +kernel)
  | exact S 2 137 4 (by decide +kernel)
  | exact S 2 137 5 (by decide +kernel)
theorem q2_138:ThresholdAt 2 138:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 138 0 (by decide +kernel)
  | exact S 2 138 1 (by decide +kernel)
  | exact S 2 138 2 (by decide +kernel)
  | exact S 2 138 3 (by decide +kernel)
  | exact S 2 138 4 (by decide +kernel)
  | exact S 2 138 5 (by decide +kernel)
theorem q2_139:ThresholdAt 2 139:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 139 0 (by decide +kernel)
  | exact S 2 139 1 (by decide +kernel)
  | exact S 2 139 2 (by decide +kernel)
  | exact S 2 139 3 (by decide +kernel)
  | exact S 2 139 4 (by decide +kernel)
  | exact S 2 139 5 (by decide +kernel)
theorem q2_140:ThresholdAt 2 140:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 140 0 (by decide +kernel)
  | exact S 2 140 1 (by decide +kernel)
  | exact S 2 140 2 (by decide +kernel)
  | exact S 2 140 3 (by decide +kernel)
  | exact S 2 140 4 (by decide +kernel)
  | exact S 2 140 5 (by decide +kernel)
theorem checkedR2:∀ V ∈ List.range 141,ThresholdAt 2 V:=by
  intro V hV
  have hv:V < 141:=List.mem_range.mp hV
  by_cases h0_141:V < 70
  · by_cases h0_70:V < 35
    · by_cases h0_35:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q2_0
              · have he:V = 1:=by omega
                subst V
                exact q2_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q2_2
              · have he:V = 3:=by omega
                subst V
                exact q2_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q2_4
              · have he:V = 5:=by omega
                subst V
                exact q2_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q2_6
              · have he:V = 7:=by omega
                subst V
                exact q2_7
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q2_8
              · have he:V = 9:=by omega
                subst V
                exact q2_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q2_10
              · have he:V = 11:=by omega
                subst V
                exact q2_11
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q2_12
              · have he:V = 13:=by omega
                subst V
                exact q2_13
            · by_cases h14_17:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q2_14
              · by_cases h15_17:V < 16
                · have he:V = 15:=by omega
                  subst V
                  exact q2_15
                · have he:V = 16:=by omega
                  subst V
                  exact q2_16
      · by_cases h17_35:V < 26
        · by_cases h17_26:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q2_17
              · have he:V = 18:=by omega
                subst V
                exact q2_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q2_19
              · have he:V = 20:=by omega
                subst V
                exact q2_20
          · by_cases h21_26:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q2_21
              · have he:V = 22:=by omega
                subst V
                exact q2_22
            · by_cases h23_26:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q2_23
              · by_cases h24_26:V < 25
                · have he:V = 24:=by omega
                  subst V
                  exact q2_24
                · have he:V = 25:=by omega
                  subst V
                  exact q2_25
        · by_cases h26_35:V < 30
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q2_26
              · have he:V = 27:=by omega
                subst V
                exact q2_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q2_28
              · have he:V = 29:=by omega
                subst V
                exact q2_29
          · by_cases h30_35:V < 32
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q2_30
              · have he:V = 31:=by omega
                subst V
                exact q2_31
            · by_cases h32_35:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q2_32
              · by_cases h33_35:V < 34
                · have he:V = 33:=by omega
                  subst V
                  exact q2_33
                · have he:V = 34:=by omega
                  subst V
                  exact q2_34
    · by_cases h35_70:V < 52
      · by_cases h35_52:V < 43
        · by_cases h35_43:V < 39
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q2_35
              · have he:V = 36:=by omega
                subst V
                exact q2_36
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q2_37
              · have he:V = 38:=by omega
                subst V
                exact q2_38
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q2_39
              · have he:V = 40:=by omega
                subst V
                exact q2_40
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q2_41
              · have he:V = 42:=by omega
                subst V
                exact q2_42
        · by_cases h43_52:V < 47
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q2_43
              · have he:V = 44:=by omega
                subst V
                exact q2_44
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q2_45
              · have he:V = 46:=by omega
                subst V
                exact q2_46
          · by_cases h47_52:V < 49
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q2_47
              · have he:V = 48:=by omega
                subst V
                exact q2_48
            · by_cases h49_52:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q2_49
              · by_cases h50_52:V < 51
                · have he:V = 50:=by omega
                  subst V
                  exact q2_50
                · have he:V = 51:=by omega
                  subst V
                  exact q2_51
      · by_cases h52_70:V < 61
        · by_cases h52_61:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q2_52
              · have he:V = 53:=by omega
                subst V
                exact q2_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q2_54
              · have he:V = 55:=by omega
                subst V
                exact q2_55
          · by_cases h56_61:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q2_56
              · have he:V = 57:=by omega
                subst V
                exact q2_57
            · by_cases h58_61:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q2_58
              · by_cases h59_61:V < 60
                · have he:V = 59:=by omega
                  subst V
                  exact q2_59
                · have he:V = 60:=by omega
                  subst V
                  exact q2_60
        · by_cases h61_70:V < 65
          · by_cases h61_65:V < 63
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q2_61
              · have he:V = 62:=by omega
                subst V
                exact q2_62
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q2_63
              · have he:V = 64:=by omega
                subst V
                exact q2_64
          · by_cases h65_70:V < 67
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q2_65
              · have he:V = 66:=by omega
                subst V
                exact q2_66
            · by_cases h67_70:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q2_67
              · by_cases h68_70:V < 69
                · have he:V = 68:=by omega
                  subst V
                  exact q2_68
                · have he:V = 69:=by omega
                  subst V
                  exact q2_69
  · by_cases h70_141:V < 105
    · by_cases h70_105:V < 87
      · by_cases h70_87:V < 78
        · by_cases h70_78:V < 74
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q2_70
              · have he:V = 71:=by omega
                subst V
                exact q2_71
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q2_72
              · have he:V = 73:=by omega
                subst V
                exact q2_73
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q2_74
              · have he:V = 75:=by omega
                subst V
                exact q2_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q2_76
              · have he:V = 77:=by omega
                subst V
                exact q2_77
        · by_cases h78_87:V < 82
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q2_78
              · have he:V = 79:=by omega
                subst V
                exact q2_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q2_80
              · have he:V = 81:=by omega
                subst V
                exact q2_81
          · by_cases h82_87:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q2_82
              · have he:V = 83:=by omega
                subst V
                exact q2_83
            · by_cases h84_87:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q2_84
              · by_cases h85_87:V < 86
                · have he:V = 85:=by omega
                  subst V
                  exact q2_85
                · have he:V = 86:=by omega
                  subst V
                  exact q2_86
      · by_cases h87_105:V < 96
        · by_cases h87_96:V < 91
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q2_87
              · have he:V = 88:=by omega
                subst V
                exact q2_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q2_89
              · have he:V = 90:=by omega
                subst V
                exact q2_90
          · by_cases h91_96:V < 93
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q2_91
              · have he:V = 92:=by omega
                subst V
                exact q2_92
            · by_cases h93_96:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q2_93
              · by_cases h94_96:V < 95
                · have he:V = 94:=by omega
                  subst V
                  exact q2_94
                · have he:V = 95:=by omega
                  subst V
                  exact q2_95
        · by_cases h96_105:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q2_96
              · have he:V = 97:=by omega
                subst V
                exact q2_97
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q2_98
              · have he:V = 99:=by omega
                subst V
                exact q2_99
          · by_cases h100_105:V < 102
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q2_100
              · have he:V = 101:=by omega
                subst V
                exact q2_101
            · by_cases h102_105:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q2_102
              · by_cases h103_105:V < 104
                · have he:V = 103:=by omega
                  subst V
                  exact q2_103
                · have he:V = 104:=by omega
                  subst V
                  exact q2_104
    · by_cases h105_141:V < 123
      · by_cases h105_123:V < 114
        · by_cases h105_114:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q2_105
              · have he:V = 106:=by omega
                subst V
                exact q2_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q2_107
              · have he:V = 108:=by omega
                subst V
                exact q2_108
          · by_cases h109_114:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q2_109
              · have he:V = 110:=by omega
                subst V
                exact q2_110
            · by_cases h111_114:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q2_111
              · by_cases h112_114:V < 113
                · have he:V = 112:=by omega
                  subst V
                  exact q2_112
                · have he:V = 113:=by omega
                  subst V
                  exact q2_113
        · by_cases h114_123:V < 118
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q2_114
              · have he:V = 115:=by omega
                subst V
                exact q2_115
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q2_116
              · have he:V = 117:=by omega
                subst V
                exact q2_117
          · by_cases h118_123:V < 120
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q2_118
              · have he:V = 119:=by omega
                subst V
                exact q2_119
            · by_cases h120_123:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q2_120
              · by_cases h121_123:V < 122
                · have he:V = 121:=by omega
                  subst V
                  exact q2_121
                · have he:V = 122:=by omega
                  subst V
                  exact q2_122
      · by_cases h123_141:V < 132
        · by_cases h123_132:V < 127
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q2_123
              · have he:V = 124:=by omega
                subst V
                exact q2_124
            · by_cases h125_127:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q2_125
              · have he:V = 126:=by omega
                subst V
                exact q2_126
          · by_cases h127_132:V < 129
            · by_cases h127_129:V < 128
              · have he:V = 127:=by omega
                subst V
                exact q2_127
              · have he:V = 128:=by omega
                subst V
                exact q2_128
            · by_cases h129_132:V < 130
              · have he:V = 129:=by omega
                subst V
                exact q2_129
              · by_cases h130_132:V < 131
                · have he:V = 130:=by omega
                  subst V
                  exact q2_130
                · have he:V = 131:=by omega
                  subst V
                  exact q2_131
        · by_cases h132_141:V < 136
          · by_cases h132_136:V < 134
            · by_cases h132_134:V < 133
              · have he:V = 132:=by omega
                subst V
                exact q2_132
              · have he:V = 133:=by omega
                subst V
                exact q2_133
            · by_cases h134_136:V < 135
              · have he:V = 134:=by omega
                subst V
                exact q2_134
              · have he:V = 135:=by omega
                subst V
                exact q2_135
          · by_cases h136_141:V < 138
            · by_cases h136_138:V < 137
              · have he:V = 136:=by omega
                subst V
                exact q2_136
              · have he:V = 137:=by omega
                subst V
                exact q2_137
            · by_cases h138_141:V < 139
              · have he:V = 138:=by omega
                subst V
                exact q2_138
              · by_cases h139_141:V < 140
                · have he:V = 139:=by omega
                  subst V
                  exact q2_139
                · have he:V = 140:=by omega
                  subst V
                  exact q2_140
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
