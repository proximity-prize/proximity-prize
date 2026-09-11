import ProximityPrize.SubmissionLower.BoundaryTailThresholdData

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q1_0:ThresholdAt 1 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 0 0 (by decide +kernel)
  | exact S 1 0 1 (by decide +kernel)
  | exact S 1 0 2 (by decide +kernel)
  | exact S 1 0 3 (by decide +kernel)
  | exact S 1 0 4 (by decide +kernel)
  | exact S 1 0 5 (by decide +kernel)
theorem q1_1:ThresholdAt 1 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 1 0 (by decide +kernel)
  | exact S 1 1 1 (by decide +kernel)
  | exact S 1 1 2 (by decide +kernel)
  | exact S 1 1 3 (by decide +kernel)
  | exact S 1 1 4 (by decide +kernel)
  | exact S 1 1 5 (by decide +kernel)
theorem q1_2:ThresholdAt 1 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 2 0 (by decide +kernel)
  | exact S 1 2 1 (by decide +kernel)
  | exact S 1 2 2 (by decide +kernel)
  | exact S 1 2 3 (by decide +kernel)
  | exact S 1 2 4 (by decide +kernel)
  | exact S 1 2 5 (by decide +kernel)
theorem q1_3:ThresholdAt 1 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 3 0 (by decide +kernel)
  | exact S 1 3 1 (by decide +kernel)
  | exact S 1 3 2 (by decide +kernel)
  | exact S 1 3 3 (by decide +kernel)
  | exact S 1 3 4 (by decide +kernel)
  | exact S 1 3 5 (by decide +kernel)
theorem q1_4:ThresholdAt 1 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 4 0 (by decide +kernel)
  | exact S 1 4 1 (by decide +kernel)
  | exact S 1 4 2 (by decide +kernel)
  | exact S 1 4 3 (by decide +kernel)
  | exact S 1 4 4 (by decide +kernel)
  | exact S 1 4 5 (by decide +kernel)
theorem q1_5:ThresholdAt 1 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 5 0 (by decide +kernel)
  | exact S 1 5 1 (by decide +kernel)
  | exact S 1 5 2 (by decide +kernel)
  | exact S 1 5 3 (by decide +kernel)
  | exact S 1 5 4 (by decide +kernel)
  | exact S 1 5 5 (by decide +kernel)
theorem q1_6:ThresholdAt 1 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 6 0 (by decide +kernel)
  | exact S 1 6 1 (by decide +kernel)
  | exact S 1 6 2 (by decide +kernel)
  | exact S 1 6 3 (by decide +kernel)
  | exact S 1 6 4 (by decide +kernel)
  | exact S 1 6 5 (by decide +kernel)
theorem q1_7:ThresholdAt 1 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 7 0 (by decide +kernel)
  | exact S 1 7 1 (by decide +kernel)
  | exact S 1 7 2 (by decide +kernel)
  | exact S 1 7 3 (by decide +kernel)
  | exact S 1 7 4 (by decide +kernel)
  | exact S 1 7 5 (by decide +kernel)
theorem q1_8:ThresholdAt 1 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 8 0 (by decide +kernel)
  | exact S 1 8 1 (by decide +kernel)
  | exact S 1 8 2 (by decide +kernel)
  | exact S 1 8 3 (by decide +kernel)
  | exact S 1 8 4 (by decide +kernel)
  | exact S 1 8 5 (by decide +kernel)
theorem q1_9:ThresholdAt 1 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 9 0 (by decide +kernel)
  | exact S 1 9 1 (by decide +kernel)
  | exact S 1 9 2 (by decide +kernel)
  | exact S 1 9 3 (by decide +kernel)
  | exact S 1 9 4 (by decide +kernel)
  | exact S 1 9 5 (by decide +kernel)
theorem q1_10:ThresholdAt 1 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 10 0 (by decide +kernel)
  | exact S 1 10 1 (by decide +kernel)
  | exact S 1 10 2 (by decide +kernel)
  | exact S 1 10 3 (by decide +kernel)
  | exact S 1 10 4 (by decide +kernel)
  | exact S 1 10 5 (by decide +kernel)
theorem q1_11:ThresholdAt 1 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 11 0 (by decide +kernel)
  | exact S 1 11 1 (by decide +kernel)
  | exact S 1 11 2 (by decide +kernel)
  | exact S 1 11 3 (by decide +kernel)
  | exact S 1 11 4 (by decide +kernel)
  | exact S 1 11 5 (by decide +kernel)
theorem q1_12:ThresholdAt 1 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 12 0 (by decide +kernel)
  | exact S 1 12 1 (by decide +kernel)
  | exact S 1 12 2 (by decide +kernel)
  | exact S 1 12 3 (by decide +kernel)
  | exact S 1 12 4 (by decide +kernel)
  | exact S 1 12 5 (by decide +kernel)
theorem q1_13:ThresholdAt 1 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 13 0 (by decide +kernel)
  | exact S 1 13 1 (by decide +kernel)
  | exact S 1 13 2 (by decide +kernel)
  | exact S 1 13 3 (by decide +kernel)
  | exact S 1 13 4 (by decide +kernel)
  | exact S 1 13 5 (by decide +kernel)
theorem q1_14:ThresholdAt 1 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 14 0 (by decide +kernel)
  | exact S 1 14 1 (by decide +kernel)
  | exact S 1 14 2 (by decide +kernel)
  | exact S 1 14 3 (by decide +kernel)
  | exact S 1 14 4 (by decide +kernel)
  | exact S 1 14 5 (by decide +kernel)
theorem q1_15:ThresholdAt 1 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 15 0 (by decide +kernel)
  | exact S 1 15 1 (by decide +kernel)
  | exact S 1 15 2 (by decide +kernel)
  | exact S 1 15 3 (by decide +kernel)
  | exact S 1 15 4 (by decide +kernel)
  | exact S 1 15 5 (by decide +kernel)
theorem q1_16:ThresholdAt 1 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 16 0 (by decide +kernel)
  | exact S 1 16 1 (by decide +kernel)
  | exact S 1 16 2 (by decide +kernel)
  | exact S 1 16 3 (by decide +kernel)
  | exact S 1 16 4 (by decide +kernel)
  | exact S 1 16 5 (by decide +kernel)
theorem q1_17:ThresholdAt 1 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 17 0 (by decide +kernel)
  | exact S 1 17 1 (by decide +kernel)
  | exact S 1 17 2 (by decide +kernel)
  | exact S 1 17 3 (by decide +kernel)
  | exact S 1 17 4 (by decide +kernel)
  | exact S 1 17 5 (by decide +kernel)
theorem q1_18:ThresholdAt 1 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 18 0 (by decide +kernel)
  | exact S 1 18 1 (by decide +kernel)
  | exact S 1 18 2 (by decide +kernel)
  | exact S 1 18 3 (by decide +kernel)
  | exact S 1 18 4 (by decide +kernel)
  | exact S 1 18 5 (by decide +kernel)
theorem q1_19:ThresholdAt 1 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 19 0 (by decide +kernel)
  | exact S 1 19 1 (by decide +kernel)
  | exact S 1 19 2 (by decide +kernel)
  | exact S 1 19 3 (by decide +kernel)
  | exact S 1 19 4 (by decide +kernel)
  | exact S 1 19 5 (by decide +kernel)
theorem q1_20:ThresholdAt 1 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 20 0 (by decide +kernel)
  | exact S 1 20 1 (by decide +kernel)
  | exact S 1 20 2 (by decide +kernel)
  | exact S 1 20 3 (by decide +kernel)
  | exact S 1 20 4 (by decide +kernel)
  | exact S 1 20 5 (by decide +kernel)
theorem q1_21:ThresholdAt 1 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 21 0 (by decide +kernel)
  | exact S 1 21 1 (by decide +kernel)
  | exact S 1 21 2 (by decide +kernel)
  | exact S 1 21 3 (by decide +kernel)
  | exact S 1 21 4 (by decide +kernel)
  | exact S 1 21 5 (by decide +kernel)
theorem q1_22:ThresholdAt 1 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 22 0 (by decide +kernel)
  | exact S 1 22 1 (by decide +kernel)
  | exact S 1 22 2 (by decide +kernel)
  | exact S 1 22 3 (by decide +kernel)
  | exact S 1 22 4 (by decide +kernel)
  | exact S 1 22 5 (by decide +kernel)
theorem q1_23:ThresholdAt 1 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 23 0 (by decide +kernel)
  | exact S 1 23 1 (by decide +kernel)
  | exact S 1 23 2 (by decide +kernel)
  | exact S 1 23 3 (by decide +kernel)
  | exact S 1 23 4 (by decide +kernel)
  | exact S 1 23 5 (by decide +kernel)
theorem q1_24:ThresholdAt 1 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 24 0 (by decide +kernel)
  | exact S 1 24 1 (by decide +kernel)
  | exact S 1 24 2 (by decide +kernel)
  | exact S 1 24 3 (by decide +kernel)
  | exact S 1 24 4 (by decide +kernel)
  | exact S 1 24 5 (by decide +kernel)
theorem q1_25:ThresholdAt 1 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 25 0 (by decide +kernel)
  | exact S 1 25 1 (by decide +kernel)
  | exact S 1 25 2 (by decide +kernel)
  | exact S 1 25 3 (by decide +kernel)
  | exact S 1 25 4 (by decide +kernel)
  | exact S 1 25 5 (by decide +kernel)
theorem q1_26:ThresholdAt 1 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 26 0 (by decide +kernel)
  | exact S 1 26 1 (by decide +kernel)
  | exact S 1 26 2 (by decide +kernel)
  | exact S 1 26 3 (by decide +kernel)
  | exact S 1 26 4 (by decide +kernel)
  | exact S 1 26 5 (by decide +kernel)
theorem q1_27:ThresholdAt 1 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 27 0 (by decide +kernel)
  | exact S 1 27 1 (by decide +kernel)
  | exact S 1 27 2 (by decide +kernel)
  | exact S 1 27 3 (by decide +kernel)
  | exact S 1 27 4 (by decide +kernel)
  | exact S 1 27 5 (by decide +kernel)
theorem q1_28:ThresholdAt 1 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 28 0 (by decide +kernel)
  | exact S 1 28 1 (by decide +kernel)
  | exact S 1 28 2 (by decide +kernel)
  | exact S 1 28 3 (by decide +kernel)
  | exact S 1 28 4 (by decide +kernel)
  | exact S 1 28 5 (by decide +kernel)
theorem q1_29:ThresholdAt 1 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 29 0 (by decide +kernel)
  | exact S 1 29 1 (by decide +kernel)
  | exact S 1 29 2 (by decide +kernel)
  | exact S 1 29 3 (by decide +kernel)
  | exact S 1 29 4 (by decide +kernel)
  | exact S 1 29 5 (by decide +kernel)
theorem q1_30:ThresholdAt 1 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 30 0 (by decide +kernel)
  | exact S 1 30 1 (by decide +kernel)
  | exact S 1 30 2 (by decide +kernel)
  | exact S 1 30 3 (by decide +kernel)
  | exact S 1 30 4 (by decide +kernel)
  | exact S 1 30 5 (by decide +kernel)
theorem q1_31:ThresholdAt 1 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 31 0 (by decide +kernel)
  | exact S 1 31 1 (by decide +kernel)
  | exact S 1 31 2 (by decide +kernel)
  | exact S 1 31 3 (by decide +kernel)
  | exact S 1 31 4 (by decide +kernel)
  | exact S 1 31 5 (by decide +kernel)
theorem q1_32:ThresholdAt 1 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 32 0 (by decide +kernel)
  | exact S 1 32 1 (by decide +kernel)
  | exact S 1 32 2 (by decide +kernel)
  | exact S 1 32 3 (by decide +kernel)
  | exact S 1 32 4 (by decide +kernel)
  | exact S 1 32 5 (by decide +kernel)
theorem q1_33:ThresholdAt 1 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 33 0 (by decide +kernel)
  | exact S 1 33 1 (by decide +kernel)
  | exact S 1 33 2 (by decide +kernel)
  | exact S 1 33 3 (by decide +kernel)
  | exact S 1 33 4 (by decide +kernel)
  | exact S 1 33 5 (by decide +kernel)
theorem q1_34:ThresholdAt 1 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 34 0 (by decide +kernel)
  | exact S 1 34 1 (by decide +kernel)
  | exact S 1 34 2 (by decide +kernel)
  | exact S 1 34 3 (by decide +kernel)
  | exact S 1 34 4 (by decide +kernel)
  | exact S 1 34 5 (by decide +kernel)
theorem q1_35:ThresholdAt 1 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 35 0 (by decide +kernel)
  | exact S 1 35 1 (by decide +kernel)
  | exact S 1 35 2 (by decide +kernel)
  | exact S 1 35 3 (by decide +kernel)
  | exact S 1 35 4 (by decide +kernel)
  | exact S 1 35 5 (by decide +kernel)
theorem q1_36:ThresholdAt 1 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 36 0 (by decide +kernel)
  | exact S 1 36 1 (by decide +kernel)
  | exact S 1 36 2 (by decide +kernel)
  | exact S 1 36 3 (by decide +kernel)
  | exact S 1 36 4 (by decide +kernel)
  | exact S 1 36 5 (by decide +kernel)
theorem q1_37:ThresholdAt 1 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 37 0 (by decide +kernel)
  | exact S 1 37 1 (by decide +kernel)
  | exact S 1 37 2 (by decide +kernel)
  | exact S 1 37 3 (by decide +kernel)
  | exact S 1 37 4 (by decide +kernel)
  | exact S 1 37 5 (by decide +kernel)
theorem q1_38:ThresholdAt 1 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 38 0 (by decide +kernel)
  | exact S 1 38 1 (by decide +kernel)
  | exact S 1 38 2 (by decide +kernel)
  | exact S 1 38 3 (by decide +kernel)
  | exact S 1 38 4 (by decide +kernel)
  | exact S 1 38 5 (by decide +kernel)
theorem q1_39:ThresholdAt 1 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 39 0 (by decide +kernel)
  | exact S 1 39 1 (by decide +kernel)
  | exact S 1 39 2 (by decide +kernel)
  | exact S 1 39 3 (by decide +kernel)
  | exact S 1 39 4 (by decide +kernel)
  | exact S 1 39 5 (by decide +kernel)
theorem q1_40:ThresholdAt 1 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 40 0 (by decide +kernel)
  | exact S 1 40 1 (by decide +kernel)
  | exact S 1 40 2 (by decide +kernel)
  | exact S 1 40 3 (by decide +kernel)
  | exact S 1 40 4 (by decide +kernel)
  | exact S 1 40 5 (by decide +kernel)
theorem q1_41:ThresholdAt 1 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 41 0 (by decide +kernel)
  | exact S 1 41 1 (by decide +kernel)
  | exact S 1 41 2 (by decide +kernel)
  | exact S 1 41 3 (by decide +kernel)
  | exact S 1 41 4 (by decide +kernel)
  | exact S 1 41 5 (by decide +kernel)
theorem q1_42:ThresholdAt 1 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 42 0 (by decide +kernel)
  | exact S 1 42 1 (by decide +kernel)
  | exact S 1 42 2 (by decide +kernel)
  | exact S 1 42 3 (by decide +kernel)
  | exact S 1 42 4 (by decide +kernel)
  | exact S 1 42 5 (by decide +kernel)
theorem q1_43:ThresholdAt 1 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 43 0 (by decide +kernel)
  | exact S 1 43 1 (by decide +kernel)
  | exact S 1 43 2 (by decide +kernel)
  | exact S 1 43 3 (by decide +kernel)
  | exact S 1 43 4 (by decide +kernel)
  | exact S 1 43 5 (by decide +kernel)
theorem q1_44:ThresholdAt 1 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 44 0 (by decide +kernel)
  | exact S 1 44 1 (by decide +kernel)
  | exact S 1 44 2 (by decide +kernel)
  | exact S 1 44 3 (by decide +kernel)
  | exact S 1 44 4 (by decide +kernel)
  | exact S 1 44 5 (by decide +kernel)
theorem q1_45:ThresholdAt 1 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 45 0 (by decide +kernel)
  | exact S 1 45 1 (by decide +kernel)
  | exact S 1 45 2 (by decide +kernel)
  | exact S 1 45 3 (by decide +kernel)
  | exact S 1 45 4 (by decide +kernel)
  | exact S 1 45 5 (by decide +kernel)
theorem q1_46:ThresholdAt 1 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 46 0 (by decide +kernel)
  | exact S 1 46 1 (by decide +kernel)
  | exact S 1 46 2 (by decide +kernel)
  | exact S 1 46 3 (by decide +kernel)
  | exact S 1 46 4 (by decide +kernel)
  | exact S 1 46 5 (by decide +kernel)
theorem q1_47:ThresholdAt 1 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 47 0 (by decide +kernel)
  | exact S 1 47 1 (by decide +kernel)
  | exact S 1 47 2 (by decide +kernel)
  | exact S 1 47 3 (by decide +kernel)
  | exact S 1 47 4 (by decide +kernel)
  | exact S 1 47 5 (by decide +kernel)
theorem q1_48:ThresholdAt 1 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 48 0 (by decide +kernel)
  | exact S 1 48 1 (by decide +kernel)
  | exact S 1 48 2 (by decide +kernel)
  | exact S 1 48 3 (by decide +kernel)
  | exact S 1 48 4 (by decide +kernel)
  | exact S 1 48 5 (by decide +kernel)
theorem q1_49:ThresholdAt 1 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 49 0 (by decide +kernel)
  | exact S 1 49 1 (by decide +kernel)
  | exact S 1 49 2 (by decide +kernel)
  | exact S 1 49 3 (by decide +kernel)
  | exact S 1 49 4 (by decide +kernel)
  | exact S 1 49 5 (by decide +kernel)
theorem q1_50:ThresholdAt 1 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 50 0 (by decide +kernel)
  | exact S 1 50 1 (by decide +kernel)
  | exact S 1 50 2 (by decide +kernel)
  | exact S 1 50 3 (by decide +kernel)
  | exact S 1 50 4 (by decide +kernel)
  | exact S 1 50 5 (by decide +kernel)
theorem q1_51:ThresholdAt 1 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 51 0 (by decide +kernel)
  | exact S 1 51 1 (by decide +kernel)
  | exact S 1 51 2 (by decide +kernel)
  | exact S 1 51 3 (by decide +kernel)
  | exact S 1 51 4 (by decide +kernel)
  | exact S 1 51 5 (by decide +kernel)
theorem q1_52:ThresholdAt 1 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 52 0 (by decide +kernel)
  | exact S 1 52 1 (by decide +kernel)
  | exact S 1 52 2 (by decide +kernel)
  | exact S 1 52 3 (by decide +kernel)
  | exact S 1 52 4 (by decide +kernel)
  | exact S 1 52 5 (by decide +kernel)
theorem q1_53:ThresholdAt 1 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 53 0 (by decide +kernel)
  | exact S 1 53 1 (by decide +kernel)
  | exact S 1 53 2 (by decide +kernel)
  | exact S 1 53 3 (by decide +kernel)
  | exact S 1 53 4 (by decide +kernel)
  | exact S 1 53 5 (by decide +kernel)
theorem q1_54:ThresholdAt 1 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 54 0 (by decide +kernel)
  | exact S 1 54 1 (by decide +kernel)
  | exact S 1 54 2 (by decide +kernel)
  | exact S 1 54 3 (by decide +kernel)
  | exact S 1 54 4 (by decide +kernel)
  | exact S 1 54 5 (by decide +kernel)
theorem q1_55:ThresholdAt 1 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 55 0 (by decide +kernel)
  | exact S 1 55 1 (by decide +kernel)
  | exact S 1 55 2 (by decide +kernel)
  | exact S 1 55 3 (by decide +kernel)
  | exact S 1 55 4 (by decide +kernel)
  | exact S 1 55 5 (by decide +kernel)
theorem q1_56:ThresholdAt 1 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 56 0 (by decide +kernel)
  | exact S 1 56 1 (by decide +kernel)
  | exact S 1 56 2 (by decide +kernel)
  | exact S 1 56 3 (by decide +kernel)
  | exact S 1 56 4 (by decide +kernel)
  | exact S 1 56 5 (by decide +kernel)
theorem q1_57:ThresholdAt 1 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 57 0 (by decide +kernel)
  | exact S 1 57 1 (by decide +kernel)
  | exact S 1 57 2 (by decide +kernel)
  | exact S 1 57 3 (by decide +kernel)
  | exact S 1 57 4 (by decide +kernel)
  | exact S 1 57 5 (by decide +kernel)
theorem q1_58:ThresholdAt 1 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 58 0 (by decide +kernel)
  | exact S 1 58 1 (by decide +kernel)
  | exact S 1 58 2 (by decide +kernel)
  | exact S 1 58 3 (by decide +kernel)
  | exact S 1 58 4 (by decide +kernel)
  | exact S 1 58 5 (by decide +kernel)
theorem q1_59:ThresholdAt 1 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 59 0 (by decide +kernel)
  | exact S 1 59 1 (by decide +kernel)
  | exact S 1 59 2 (by decide +kernel)
  | exact S 1 59 3 (by decide +kernel)
  | exact S 1 59 4 (by decide +kernel)
  | exact S 1 59 5 (by decide +kernel)
theorem q1_60:ThresholdAt 1 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 60 0 (by decide +kernel)
  | exact S 1 60 1 (by decide +kernel)
  | exact S 1 60 2 (by decide +kernel)
  | exact S 1 60 3 (by decide +kernel)
  | exact S 1 60 4 (by decide +kernel)
  | exact S 1 60 5 (by decide +kernel)
theorem q1_61:ThresholdAt 1 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 61 0 (by decide +kernel)
  | exact S 1 61 1 (by decide +kernel)
  | exact S 1 61 2 (by decide +kernel)
  | exact S 1 61 3 (by decide +kernel)
  | exact S 1 61 4 (by decide +kernel)
  | exact S 1 61 5 (by decide +kernel)
theorem q1_62:ThresholdAt 1 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 62 0 (by decide +kernel)
  | exact S 1 62 1 (by decide +kernel)
  | exact S 1 62 2 (by decide +kernel)
  | exact S 1 62 3 (by decide +kernel)
  | exact S 1 62 4 (by decide +kernel)
  | exact S 1 62 5 (by decide +kernel)
theorem q1_63:ThresholdAt 1 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 63 0 (by decide +kernel)
  | exact S 1 63 1 (by decide +kernel)
  | exact S 1 63 2 (by decide +kernel)
  | exact S 1 63 3 (by decide +kernel)
  | exact S 1 63 4 (by decide +kernel)
  | exact S 1 63 5 (by decide +kernel)
theorem q1_64:ThresholdAt 1 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 64 0 (by decide +kernel)
  | exact S 1 64 1 (by decide +kernel)
  | exact S 1 64 2 (by decide +kernel)
  | exact S 1 64 3 (by decide +kernel)
  | exact S 1 64 4 (by decide +kernel)
  | exact S 1 64 5 (by decide +kernel)
theorem q1_65:ThresholdAt 1 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 65 0 (by decide +kernel)
  | exact S 1 65 1 (by decide +kernel)
  | exact S 1 65 2 (by decide +kernel)
  | exact S 1 65 3 (by decide +kernel)
  | exact S 1 65 4 (by decide +kernel)
  | exact S 1 65 5 (by decide +kernel)
theorem q1_66:ThresholdAt 1 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 66 0 (by decide +kernel)
  | exact S 1 66 1 (by decide +kernel)
  | exact S 1 66 2 (by decide +kernel)
  | exact S 1 66 3 (by decide +kernel)
  | exact S 1 66 4 (by decide +kernel)
  | exact S 1 66 5 (by decide +kernel)
theorem q1_67:ThresholdAt 1 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 67 0 (by decide +kernel)
  | exact S 1 67 1 (by decide +kernel)
  | exact S 1 67 2 (by decide +kernel)
  | exact S 1 67 3 (by decide +kernel)
  | exact S 1 67 4 (by decide +kernel)
  | exact S 1 67 5 (by decide +kernel)
theorem q1_68:ThresholdAt 1 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 68 0 (by decide +kernel)
  | exact S 1 68 1 (by decide +kernel)
  | exact S 1 68 2 (by decide +kernel)
  | exact S 1 68 3 (by decide +kernel)
  | exact S 1 68 4 (by decide +kernel)
  | exact S 1 68 5 (by decide +kernel)
theorem q1_69:ThresholdAt 1 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 69 0 (by decide +kernel)
  | exact S 1 69 1 (by decide +kernel)
  | exact S 1 69 2 (by decide +kernel)
  | exact S 1 69 3 (by decide +kernel)
  | exact S 1 69 4 (by decide +kernel)
  | exact S 1 69 5 (by decide +kernel)
theorem q1_70:ThresholdAt 1 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 70 0 (by decide +kernel)
  | exact S 1 70 1 (by decide +kernel)
  | exact S 1 70 2 (by decide +kernel)
  | exact S 1 70 3 (by decide +kernel)
  | exact S 1 70 4 (by decide +kernel)
  | exact S 1 70 5 (by decide +kernel)
theorem q1_71:ThresholdAt 1 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 71 0 (by decide +kernel)
  | exact S 1 71 1 (by decide +kernel)
  | exact S 1 71 2 (by decide +kernel)
  | exact S 1 71 3 (by decide +kernel)
  | exact S 1 71 4 (by decide +kernel)
  | exact S 1 71 5 (by decide +kernel)
theorem q1_72:ThresholdAt 1 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 72 0 (by decide +kernel)
  | exact S 1 72 1 (by decide +kernel)
  | exact S 1 72 2 (by decide +kernel)
  | exact S 1 72 3 (by decide +kernel)
  | exact S 1 72 4 (by decide +kernel)
  | exact S 1 72 5 (by decide +kernel)
theorem q1_73:ThresholdAt 1 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 73 0 (by decide +kernel)
  | exact S 1 73 1 (by decide +kernel)
  | exact S 1 73 2 (by decide +kernel)
  | exact S 1 73 3 (by decide +kernel)
  | exact S 1 73 4 (by decide +kernel)
  | exact S 1 73 5 (by decide +kernel)
theorem q1_74:ThresholdAt 1 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 74 0 (by decide +kernel)
  | exact S 1 74 1 (by decide +kernel)
  | exact S 1 74 2 (by decide +kernel)
  | exact S 1 74 3 (by decide +kernel)
  | exact S 1 74 4 (by decide +kernel)
  | exact S 1 74 5 (by decide +kernel)
theorem q1_75:ThresholdAt 1 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 75 0 (by decide +kernel)
  | exact S 1 75 1 (by decide +kernel)
  | exact S 1 75 2 (by decide +kernel)
  | exact S 1 75 3 (by decide +kernel)
  | exact S 1 75 4 (by decide +kernel)
  | exact S 1 75 5 (by decide +kernel)
theorem q1_76:ThresholdAt 1 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 76 0 (by decide +kernel)
  | exact S 1 76 1 (by decide +kernel)
  | exact S 1 76 2 (by decide +kernel)
  | exact S 1 76 3 (by decide +kernel)
  | exact S 1 76 4 (by decide +kernel)
  | exact S 1 76 5 (by decide +kernel)
theorem q1_77:ThresholdAt 1 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 77 0 (by decide +kernel)
  | exact S 1 77 1 (by decide +kernel)
  | exact S 1 77 2 (by decide +kernel)
  | exact S 1 77 3 (by decide +kernel)
  | exact S 1 77 4 (by decide +kernel)
  | exact S 1 77 5 (by decide +kernel)
theorem q1_78:ThresholdAt 1 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 78 0 (by decide +kernel)
  | exact S 1 78 1 (by decide +kernel)
  | exact S 1 78 2 (by decide +kernel)
  | exact S 1 78 3 (by decide +kernel)
  | exact S 1 78 4 (by decide +kernel)
  | exact S 1 78 5 (by decide +kernel)
theorem q1_79:ThresholdAt 1 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 79 0 (by decide +kernel)
  | exact S 1 79 1 (by decide +kernel)
  | exact S 1 79 2 (by decide +kernel)
  | exact S 1 79 3 (by decide +kernel)
  | exact S 1 79 4 (by decide +kernel)
  | exact S 1 79 5 (by decide +kernel)
theorem q1_80:ThresholdAt 1 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 80 0 (by decide +kernel)
  | exact S 1 80 1 (by decide +kernel)
  | exact S 1 80 2 (by decide +kernel)
  | exact S 1 80 3 (by decide +kernel)
  | exact S 1 80 4 (by decide +kernel)
  | exact S 1 80 5 (by decide +kernel)
theorem q1_81:ThresholdAt 1 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 81 0 (by decide +kernel)
  | exact S 1 81 1 (by decide +kernel)
  | exact S 1 81 2 (by decide +kernel)
  | exact S 1 81 3 (by decide +kernel)
  | exact S 1 81 4 (by decide +kernel)
  | exact S 1 81 5 (by decide +kernel)
theorem q1_82:ThresholdAt 1 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 82 0 (by decide +kernel)
  | exact S 1 82 1 (by decide +kernel)
  | exact S 1 82 2 (by decide +kernel)
  | exact S 1 82 3 (by decide +kernel)
  | exact S 1 82 4 (by decide +kernel)
  | exact S 1 82 5 (by decide +kernel)
theorem q1_83:ThresholdAt 1 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 83 0 (by decide +kernel)
  | exact S 1 83 1 (by decide +kernel)
  | exact S 1 83 2 (by decide +kernel)
  | exact S 1 83 3 (by decide +kernel)
  | exact S 1 83 4 (by decide +kernel)
  | exact S 1 83 5 (by decide +kernel)
theorem q1_84:ThresholdAt 1 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 84 0 (by decide +kernel)
  | exact S 1 84 1 (by decide +kernel)
  | exact S 1 84 2 (by decide +kernel)
  | exact S 1 84 3 (by decide +kernel)
  | exact S 1 84 4 (by decide +kernel)
  | exact S 1 84 5 (by decide +kernel)
theorem q1_85:ThresholdAt 1 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 85 0 (by decide +kernel)
  | exact S 1 85 1 (by decide +kernel)
  | exact S 1 85 2 (by decide +kernel)
  | exact S 1 85 3 (by decide +kernel)
  | exact S 1 85 4 (by decide +kernel)
  | exact S 1 85 5 (by decide +kernel)
theorem q1_86:ThresholdAt 1 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 86 0 (by decide +kernel)
  | exact S 1 86 1 (by decide +kernel)
  | exact S 1 86 2 (by decide +kernel)
  | exact S 1 86 3 (by decide +kernel)
  | exact S 1 86 4 (by decide +kernel)
  | exact S 1 86 5 (by decide +kernel)
theorem q1_87:ThresholdAt 1 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 87 0 (by decide +kernel)
  | exact S 1 87 1 (by decide +kernel)
  | exact S 1 87 2 (by decide +kernel)
  | exact S 1 87 3 (by decide +kernel)
  | exact S 1 87 4 (by decide +kernel)
  | exact S 1 87 5 (by decide +kernel)
theorem q1_88:ThresholdAt 1 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 88 0 (by decide +kernel)
  | exact S 1 88 1 (by decide +kernel)
  | exact S 1 88 2 (by decide +kernel)
  | exact S 1 88 3 (by decide +kernel)
  | exact S 1 88 4 (by decide +kernel)
  | exact S 1 88 5 (by decide +kernel)
theorem q1_89:ThresholdAt 1 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 89 0 (by decide +kernel)
  | exact S 1 89 1 (by decide +kernel)
  | exact S 1 89 2 (by decide +kernel)
  | exact S 1 89 3 (by decide +kernel)
  | exact S 1 89 4 (by decide +kernel)
  | exact S 1 89 5 (by decide +kernel)
theorem q1_90:ThresholdAt 1 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 90 0 (by decide +kernel)
  | exact S 1 90 1 (by decide +kernel)
  | exact S 1 90 2 (by decide +kernel)
  | exact S 1 90 3 (by decide +kernel)
  | exact S 1 90 4 (by decide +kernel)
  | exact S 1 90 5 (by decide +kernel)
theorem q1_91:ThresholdAt 1 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 91 0 (by decide +kernel)
  | exact S 1 91 1 (by decide +kernel)
  | exact S 1 91 2 (by decide +kernel)
  | exact S 1 91 3 (by decide +kernel)
  | exact S 1 91 4 (by decide +kernel)
  | exact S 1 91 5 (by decide +kernel)
theorem q1_92:ThresholdAt 1 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 92 0 (by decide +kernel)
  | exact S 1 92 1 (by decide +kernel)
  | exact S 1 92 2 (by decide +kernel)
  | exact S 1 92 3 (by decide +kernel)
  | exact S 1 92 4 (by decide +kernel)
  | exact S 1 92 5 (by decide +kernel)
theorem q1_93:ThresholdAt 1 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 93 0 (by decide +kernel)
  | exact S 1 93 1 (by decide +kernel)
  | exact S 1 93 2 (by decide +kernel)
  | exact S 1 93 3 (by decide +kernel)
  | exact S 1 93 4 (by decide +kernel)
  | exact S 1 93 5 (by decide +kernel)
theorem q1_94:ThresholdAt 1 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 94 0 (by decide +kernel)
  | exact S 1 94 1 (by decide +kernel)
  | exact S 1 94 2 (by decide +kernel)
  | exact S 1 94 3 (by decide +kernel)
  | exact S 1 94 4 (by decide +kernel)
  | exact S 1 94 5 (by decide +kernel)
theorem q1_95:ThresholdAt 1 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 95 0 (by decide +kernel)
  | exact S 1 95 1 (by decide +kernel)
  | exact S 1 95 2 (by decide +kernel)
  | exact S 1 95 3 (by decide +kernel)
  | exact S 1 95 4 (by decide +kernel)
  | exact S 1 95 5 (by decide +kernel)
theorem q1_96:ThresholdAt 1 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 96 0 (by decide +kernel)
  | exact S 1 96 1 (by decide +kernel)
  | exact S 1 96 2 (by decide +kernel)
  | exact S 1 96 3 (by decide +kernel)
  | exact S 1 96 4 (by decide +kernel)
  | exact S 1 96 5 (by decide +kernel)
theorem q1_97:ThresholdAt 1 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 97 0 (by decide +kernel)
  | exact S 1 97 1 (by decide +kernel)
  | exact S 1 97 2 (by decide +kernel)
  | exact S 1 97 3 (by decide +kernel)
  | exact S 1 97 4 (by decide +kernel)
  | exact S 1 97 5 (by decide +kernel)
theorem q1_98:ThresholdAt 1 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 98 0 (by decide +kernel)
  | exact S 1 98 1 (by decide +kernel)
  | exact S 1 98 2 (by decide +kernel)
  | exact S 1 98 3 (by decide +kernel)
  | exact S 1 98 4 (by decide +kernel)
  | exact S 1 98 5 (by decide +kernel)
theorem q1_99:ThresholdAt 1 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 99 0 (by decide +kernel)
  | exact S 1 99 1 (by decide +kernel)
  | exact S 1 99 2 (by decide +kernel)
  | exact S 1 99 3 (by decide +kernel)
  | exact S 1 99 4 (by decide +kernel)
  | exact S 1 99 5 (by decide +kernel)
theorem q1_100:ThresholdAt 1 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 100 0 (by decide +kernel)
  | exact S 1 100 1 (by decide +kernel)
  | exact S 1 100 2 (by decide +kernel)
  | exact S 1 100 3 (by decide +kernel)
  | exact S 1 100 4 (by decide +kernel)
  | exact S 1 100 5 (by decide +kernel)
theorem q1_101:ThresholdAt 1 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 101 0 (by decide +kernel)
  | exact S 1 101 1 (by decide +kernel)
  | exact S 1 101 2 (by decide +kernel)
  | exact S 1 101 3 (by decide +kernel)
  | exact S 1 101 4 (by decide +kernel)
  | exact S 1 101 5 (by decide +kernel)
theorem q1_102:ThresholdAt 1 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 102 0 (by decide +kernel)
  | exact S 1 102 1 (by decide +kernel)
  | exact S 1 102 2 (by decide +kernel)
  | exact S 1 102 3 (by decide +kernel)
  | exact S 1 102 4 (by decide +kernel)
  | exact S 1 102 5 (by decide +kernel)
theorem q1_103:ThresholdAt 1 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 103 0 (by decide +kernel)
  | exact S 1 103 1 (by decide +kernel)
  | exact S 1 103 2 (by decide +kernel)
  | exact S 1 103 3 (by decide +kernel)
  | exact S 1 103 4 (by decide +kernel)
  | exact S 1 103 5 (by decide +kernel)
theorem q1_104:ThresholdAt 1 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 104 0 (by decide +kernel)
  | exact S 1 104 1 (by decide +kernel)
  | exact S 1 104 2 (by decide +kernel)
  | exact S 1 104 3 (by decide +kernel)
  | exact S 1 104 4 (by decide +kernel)
  | exact S 1 104 5 (by decide +kernel)
theorem q1_105:ThresholdAt 1 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 105 0 (by decide +kernel)
  | exact S 1 105 1 (by decide +kernel)
  | exact S 1 105 2 (by decide +kernel)
  | exact S 1 105 3 (by decide +kernel)
  | exact S 1 105 4 (by decide +kernel)
  | exact S 1 105 5 (by decide +kernel)
theorem q1_106:ThresholdAt 1 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 106 0 (by decide +kernel)
  | exact S 1 106 1 (by decide +kernel)
  | exact S 1 106 2 (by decide +kernel)
  | exact S 1 106 3 (by decide +kernel)
  | exact S 1 106 4 (by decide +kernel)
  | exact S 1 106 5 (by decide +kernel)
theorem q1_107:ThresholdAt 1 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 107 0 (by decide +kernel)
  | exact S 1 107 1 (by decide +kernel)
  | exact S 1 107 2 (by decide +kernel)
  | exact S 1 107 3 (by decide +kernel)
  | exact S 1 107 4 (by decide +kernel)
  | exact S 1 107 5 (by decide +kernel)
theorem q1_108:ThresholdAt 1 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 108 0 (by decide +kernel)
  | exact S 1 108 1 (by decide +kernel)
  | exact S 1 108 2 (by decide +kernel)
  | exact S 1 108 3 (by decide +kernel)
  | exact S 1 108 4 (by decide +kernel)
  | exact S 1 108 5 (by decide +kernel)
theorem q1_109:ThresholdAt 1 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 109 0 (by decide +kernel)
  | exact S 1 109 1 (by decide +kernel)
  | exact S 1 109 2 (by decide +kernel)
  | exact S 1 109 3 (by decide +kernel)
  | exact S 1 109 4 (by decide +kernel)
  | exact S 1 109 5 (by decide +kernel)
theorem q1_110:ThresholdAt 1 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 110 0 (by decide +kernel)
  | exact S 1 110 1 (by decide +kernel)
  | exact S 1 110 2 (by decide +kernel)
  | exact S 1 110 3 (by decide +kernel)
  | exact S 1 110 4 (by decide +kernel)
  | exact S 1 110 5 (by decide +kernel)
theorem q1_111:ThresholdAt 1 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 111 0 (by decide +kernel)
  | exact S 1 111 1 (by decide +kernel)
  | exact S 1 111 2 (by decide +kernel)
  | exact S 1 111 3 (by decide +kernel)
  | exact S 1 111 4 (by decide +kernel)
  | exact S 1 111 5 (by decide +kernel)
theorem q1_112:ThresholdAt 1 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 112 0 (by decide +kernel)
  | exact S 1 112 1 (by decide +kernel)
  | exact S 1 112 2 (by decide +kernel)
  | exact S 1 112 3 (by decide +kernel)
  | exact S 1 112 4 (by decide +kernel)
  | exact S 1 112 5 (by decide +kernel)
theorem q1_113:ThresholdAt 1 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 113 0 (by decide +kernel)
  | exact S 1 113 1 (by decide +kernel)
  | exact S 1 113 2 (by decide +kernel)
  | exact S 1 113 3 (by decide +kernel)
  | exact S 1 113 4 (by decide +kernel)
  | exact S 1 113 5 (by decide +kernel)
theorem q1_114:ThresholdAt 1 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 114 0 (by decide +kernel)
  | exact S 1 114 1 (by decide +kernel)
  | exact S 1 114 2 (by decide +kernel)
  | exact S 1 114 3 (by decide +kernel)
  | exact S 1 114 4 (by decide +kernel)
  | exact S 1 114 5 (by decide +kernel)
theorem q1_115:ThresholdAt 1 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 115 0 (by decide +kernel)
  | exact S 1 115 1 (by decide +kernel)
  | exact S 1 115 2 (by decide +kernel)
  | exact S 1 115 3 (by decide +kernel)
  | exact S 1 115 4 (by decide +kernel)
  | exact S 1 115 5 (by decide +kernel)
theorem q1_116:ThresholdAt 1 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 116 0 (by decide +kernel)
  | exact S 1 116 1 (by decide +kernel)
  | exact S 1 116 2 (by decide +kernel)
  | exact S 1 116 3 (by decide +kernel)
  | exact S 1 116 4 (by decide +kernel)
  | exact S 1 116 5 (by decide +kernel)
theorem q1_117:ThresholdAt 1 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 117 0 (by decide +kernel)
  | exact S 1 117 1 (by decide +kernel)
  | exact S 1 117 2 (by decide +kernel)
  | exact S 1 117 3 (by decide +kernel)
  | exact S 1 117 4 (by decide +kernel)
  | exact S 1 117 5 (by decide +kernel)
theorem q1_118:ThresholdAt 1 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 118 0 (by decide +kernel)
  | exact S 1 118 1 (by decide +kernel)
  | exact S 1 118 2 (by decide +kernel)
  | exact S 1 118 3 (by decide +kernel)
  | exact S 1 118 4 (by decide +kernel)
  | exact S 1 118 5 (by decide +kernel)
theorem q1_119:ThresholdAt 1 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 119 0 (by decide +kernel)
  | exact S 1 119 1 (by decide +kernel)
  | exact S 1 119 2 (by decide +kernel)
  | exact S 1 119 3 (by decide +kernel)
  | exact S 1 119 4 (by decide +kernel)
  | exact S 1 119 5 (by decide +kernel)
theorem q1_120:ThresholdAt 1 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 120 0 (by decide +kernel)
  | exact S 1 120 1 (by decide +kernel)
  | exact S 1 120 2 (by decide +kernel)
  | exact S 1 120 3 (by decide +kernel)
  | exact S 1 120 4 (by decide +kernel)
  | exact S 1 120 5 (by decide +kernel)
theorem q1_121:ThresholdAt 1 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 121 0 (by decide +kernel)
  | exact S 1 121 1 (by decide +kernel)
  | exact S 1 121 2 (by decide +kernel)
  | exact S 1 121 3 (by decide +kernel)
  | exact S 1 121 4 (by decide +kernel)
  | exact S 1 121 5 (by decide +kernel)
theorem q1_122:ThresholdAt 1 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 122 0 (by decide +kernel)
  | exact S 1 122 1 (by decide +kernel)
  | exact S 1 122 2 (by decide +kernel)
  | exact S 1 122 3 (by decide +kernel)
  | exact S 1 122 4 (by decide +kernel)
  | exact S 1 122 5 (by decide +kernel)
theorem q1_123:ThresholdAt 1 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 123 0 (by decide +kernel)
  | exact S 1 123 1 (by decide +kernel)
  | exact S 1 123 2 (by decide +kernel)
  | exact S 1 123 3 (by decide +kernel)
  | exact S 1 123 4 (by decide +kernel)
  | exact S 1 123 5 (by decide +kernel)
theorem q1_124:ThresholdAt 1 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 124 0 (by decide +kernel)
  | exact S 1 124 1 (by decide +kernel)
  | exact S 1 124 2 (by decide +kernel)
  | exact S 1 124 3 (by decide +kernel)
  | exact S 1 124 4 (by decide +kernel)
  | exact S 1 124 5 (by decide +kernel)
theorem q1_125:ThresholdAt 1 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 125 0 (by decide +kernel)
  | exact S 1 125 1 (by decide +kernel)
  | exact S 1 125 2 (by decide +kernel)
  | exact S 1 125 3 (by decide +kernel)
  | exact S 1 125 4 (by decide +kernel)
  | exact S 1 125 5 (by decide +kernel)
theorem q1_126:ThresholdAt 1 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 126 0 (by decide +kernel)
  | exact S 1 126 1 (by decide +kernel)
  | exact S 1 126 2 (by decide +kernel)
  | exact S 1 126 3 (by decide +kernel)
  | exact S 1 126 4 (by decide +kernel)
  | exact S 1 126 5 (by decide +kernel)
theorem q1_127:ThresholdAt 1 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 127 0 (by decide +kernel)
  | exact S 1 127 1 (by decide +kernel)
  | exact S 1 127 2 (by decide +kernel)
  | exact S 1 127 3 (by decide +kernel)
  | exact S 1 127 4 (by decide +kernel)
  | exact S 1 127 5 (by decide +kernel)
theorem q1_128:ThresholdAt 1 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 128 0 (by decide +kernel)
  | exact S 1 128 1 (by decide +kernel)
  | exact S 1 128 2 (by decide +kernel)
  | exact S 1 128 3 (by decide +kernel)
  | exact S 1 128 4 (by decide +kernel)
  | exact S 1 128 5 (by decide +kernel)
theorem q1_129:ThresholdAt 1 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 129 0 (by decide +kernel)
  | exact S 1 129 1 (by decide +kernel)
  | exact S 1 129 2 (by decide +kernel)
  | exact S 1 129 3 (by decide +kernel)
  | exact S 1 129 4 (by decide +kernel)
  | exact S 1 129 5 (by decide +kernel)
theorem q1_130:ThresholdAt 1 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 130 0 (by decide +kernel)
  | exact S 1 130 1 (by decide +kernel)
  | exact S 1 130 2 (by decide +kernel)
  | exact S 1 130 3 (by decide +kernel)
  | exact S 1 130 4 (by decide +kernel)
  | exact S 1 130 5 (by decide +kernel)
theorem q1_131:ThresholdAt 1 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 131 0 (by decide +kernel)
  | exact S 1 131 1 (by decide +kernel)
  | exact S 1 131 2 (by decide +kernel)
  | exact S 1 131 3 (by decide +kernel)
  | exact S 1 131 4 (by decide +kernel)
  | exact S 1 131 5 (by decide +kernel)
theorem q1_132:ThresholdAt 1 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 132 0 (by decide +kernel)
  | exact S 1 132 1 (by decide +kernel)
  | exact S 1 132 2 (by decide +kernel)
  | exact S 1 132 3 (by decide +kernel)
  | exact S 1 132 4 (by decide +kernel)
  | exact S 1 132 5 (by decide +kernel)
theorem q1_133:ThresholdAt 1 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 133 0 (by decide +kernel)
  | exact S 1 133 1 (by decide +kernel)
  | exact S 1 133 2 (by decide +kernel)
  | exact S 1 133 3 (by decide +kernel)
  | exact S 1 133 4 (by decide +kernel)
  | exact S 1 133 5 (by decide +kernel)
theorem q1_134:ThresholdAt 1 134:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 134 0 (by decide +kernel)
  | exact S 1 134 1 (by decide +kernel)
  | exact S 1 134 2 (by decide +kernel)
  | exact S 1 134 3 (by decide +kernel)
  | exact S 1 134 4 (by decide +kernel)
  | exact S 1 134 5 (by decide +kernel)
theorem q1_135:ThresholdAt 1 135:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 135 0 (by decide +kernel)
  | exact S 1 135 1 (by decide +kernel)
  | exact S 1 135 2 (by decide +kernel)
  | exact S 1 135 3 (by decide +kernel)
  | exact S 1 135 4 (by decide +kernel)
  | exact S 1 135 5 (by decide +kernel)
theorem q1_136:ThresholdAt 1 136:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 136 0 (by decide +kernel)
  | exact S 1 136 1 (by decide +kernel)
  | exact S 1 136 2 (by decide +kernel)
  | exact S 1 136 3 (by decide +kernel)
  | exact S 1 136 4 (by decide +kernel)
  | exact S 1 136 5 (by decide +kernel)
theorem q1_137:ThresholdAt 1 137:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 137 0 (by decide +kernel)
  | exact S 1 137 1 (by decide +kernel)
  | exact S 1 137 2 (by decide +kernel)
  | exact S 1 137 3 (by decide +kernel)
  | exact S 1 137 4 (by decide +kernel)
  | exact S 1 137 5 (by decide +kernel)
theorem q1_138:ThresholdAt 1 138:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 138 0 (by decide +kernel)
  | exact S 1 138 1 (by decide +kernel)
  | exact S 1 138 2 (by decide +kernel)
  | exact S 1 138 3 (by decide +kernel)
  | exact S 1 138 4 (by decide +kernel)
  | exact S 1 138 5 (by decide +kernel)
theorem q1_139:ThresholdAt 1 139:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 139 0 (by decide +kernel)
  | exact S 1 139 1 (by decide +kernel)
  | exact S 1 139 2 (by decide +kernel)
  | exact S 1 139 3 (by decide +kernel)
  | exact S 1 139 4 (by decide +kernel)
  | exact S 1 139 5 (by decide +kernel)
theorem q1_140:ThresholdAt 1 140:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 140 0 (by decide +kernel)
  | exact S 1 140 1 (by decide +kernel)
  | exact S 1 140 2 (by decide +kernel)
  | exact S 1 140 3 (by decide +kernel)
  | exact S 1 140 4 (by decide +kernel)
  | exact S 1 140 5 (by decide +kernel)
theorem q1_141:ThresholdAt 1 141:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 141 0 (by decide +kernel)
  | exact S 1 141 1 (by decide +kernel)
  | exact S 1 141 2 (by decide +kernel)
  | exact S 1 141 3 (by decide +kernel)
  | exact S 1 141 4 (by decide +kernel)
  | exact S 1 141 5 (by decide +kernel)
theorem checkedR1:∀ V ∈ List.range 142,ThresholdAt 1 V:=by
  intro V hV
  have hv:V < 142:=List.mem_range.mp hV
  by_cases h0_142:V < 71
  · by_cases h0_71:V < 35
    · by_cases h0_35:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q1_0
              · have he:V = 1:=by omega
                subst V
                exact q1_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q1_2
              · have he:V = 3:=by omega
                subst V
                exact q1_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q1_4
              · have he:V = 5:=by omega
                subst V
                exact q1_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q1_6
              · have he:V = 7:=by omega
                subst V
                exact q1_7
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q1_8
              · have he:V = 9:=by omega
                subst V
                exact q1_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q1_10
              · have he:V = 11:=by omega
                subst V
                exact q1_11
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q1_12
              · have he:V = 13:=by omega
                subst V
                exact q1_13
            · by_cases h14_17:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q1_14
              · by_cases h15_17:V < 16
                · have he:V = 15:=by omega
                  subst V
                  exact q1_15
                · have he:V = 16:=by omega
                  subst V
                  exact q1_16
      · by_cases h17_35:V < 26
        · by_cases h17_26:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q1_17
              · have he:V = 18:=by omega
                subst V
                exact q1_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q1_19
              · have he:V = 20:=by omega
                subst V
                exact q1_20
          · by_cases h21_26:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q1_21
              · have he:V = 22:=by omega
                subst V
                exact q1_22
            · by_cases h23_26:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q1_23
              · by_cases h24_26:V < 25
                · have he:V = 24:=by omega
                  subst V
                  exact q1_24
                · have he:V = 25:=by omega
                  subst V
                  exact q1_25
        · by_cases h26_35:V < 30
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q1_26
              · have he:V = 27:=by omega
                subst V
                exact q1_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q1_28
              · have he:V = 29:=by omega
                subst V
                exact q1_29
          · by_cases h30_35:V < 32
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q1_30
              · have he:V = 31:=by omega
                subst V
                exact q1_31
            · by_cases h32_35:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q1_32
              · by_cases h33_35:V < 34
                · have he:V = 33:=by omega
                  subst V
                  exact q1_33
                · have he:V = 34:=by omega
                  subst V
                  exact q1_34
    · by_cases h35_71:V < 53
      · by_cases h35_53:V < 44
        · by_cases h35_44:V < 39
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q1_35
              · have he:V = 36:=by omega
                subst V
                exact q1_36
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q1_37
              · have he:V = 38:=by omega
                subst V
                exact q1_38
          · by_cases h39_44:V < 41
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q1_39
              · have he:V = 40:=by omega
                subst V
                exact q1_40
            · by_cases h41_44:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q1_41
              · by_cases h42_44:V < 43
                · have he:V = 42:=by omega
                  subst V
                  exact q1_42
                · have he:V = 43:=by omega
                  subst V
                  exact q1_43
        · by_cases h44_53:V < 48
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q1_44
              · have he:V = 45:=by omega
                subst V
                exact q1_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q1_46
              · have he:V = 47:=by omega
                subst V
                exact q1_47
          · by_cases h48_53:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q1_48
              · have he:V = 49:=by omega
                subst V
                exact q1_49
            · by_cases h50_53:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q1_50
              · by_cases h51_53:V < 52
                · have he:V = 51:=by omega
                  subst V
                  exact q1_51
                · have he:V = 52:=by omega
                  subst V
                  exact q1_52
      · by_cases h53_71:V < 62
        · by_cases h53_62:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q1_53
              · have he:V = 54:=by omega
                subst V
                exact q1_54
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q1_55
              · have he:V = 56:=by omega
                subst V
                exact q1_56
          · by_cases h57_62:V < 59
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q1_57
              · have he:V = 58:=by omega
                subst V
                exact q1_58
            · by_cases h59_62:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q1_59
              · by_cases h60_62:V < 61
                · have he:V = 60:=by omega
                  subst V
                  exact q1_60
                · have he:V = 61:=by omega
                  subst V
                  exact q1_61
        · by_cases h62_71:V < 66
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q1_62
              · have he:V = 63:=by omega
                subst V
                exact q1_63
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q1_64
              · have he:V = 65:=by omega
                subst V
                exact q1_65
          · by_cases h66_71:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q1_66
              · have he:V = 67:=by omega
                subst V
                exact q1_67
            · by_cases h68_71:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q1_68
              · by_cases h69_71:V < 70
                · have he:V = 69:=by omega
                  subst V
                  exact q1_69
                · have he:V = 70:=by omega
                  subst V
                  exact q1_70
  · by_cases h71_142:V < 106
    · by_cases h71_106:V < 88
      · by_cases h71_88:V < 79
        · by_cases h71_79:V < 75
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q1_71
              · have he:V = 72:=by omega
                subst V
                exact q1_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q1_73
              · have he:V = 74:=by omega
                subst V
                exact q1_74
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q1_75
              · have he:V = 76:=by omega
                subst V
                exact q1_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q1_77
              · have he:V = 78:=by omega
                subst V
                exact q1_78
        · by_cases h79_88:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q1_79
              · have he:V = 80:=by omega
                subst V
                exact q1_80
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q1_81
              · have he:V = 82:=by omega
                subst V
                exact q1_82
          · by_cases h83_88:V < 85
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q1_83
              · have he:V = 84:=by omega
                subst V
                exact q1_84
            · by_cases h85_88:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q1_85
              · by_cases h86_88:V < 87
                · have he:V = 86:=by omega
                  subst V
                  exact q1_86
                · have he:V = 87:=by omega
                  subst V
                  exact q1_87
      · by_cases h88_106:V < 97
        · by_cases h88_97:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q1_88
              · have he:V = 89:=by omega
                subst V
                exact q1_89
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q1_90
              · have he:V = 91:=by omega
                subst V
                exact q1_91
          · by_cases h92_97:V < 94
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q1_92
              · have he:V = 93:=by omega
                subst V
                exact q1_93
            · by_cases h94_97:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q1_94
              · by_cases h95_97:V < 96
                · have he:V = 95:=by omega
                  subst V
                  exact q1_95
                · have he:V = 96:=by omega
                  subst V
                  exact q1_96
        · by_cases h97_106:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q1_97
              · have he:V = 98:=by omega
                subst V
                exact q1_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q1_99
              · have he:V = 100:=by omega
                subst V
                exact q1_100
          · by_cases h101_106:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q1_101
              · have he:V = 102:=by omega
                subst V
                exact q1_102
            · by_cases h103_106:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q1_103
              · by_cases h104_106:V < 105
                · have he:V = 104:=by omega
                  subst V
                  exact q1_104
                · have he:V = 105:=by omega
                  subst V
                  exact q1_105
    · by_cases h106_142:V < 124
      · by_cases h106_124:V < 115
        · by_cases h106_115:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q1_106
              · have he:V = 107:=by omega
                subst V
                exact q1_107
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q1_108
              · have he:V = 109:=by omega
                subst V
                exact q1_109
          · by_cases h110_115:V < 112
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q1_110
              · have he:V = 111:=by omega
                subst V
                exact q1_111
            · by_cases h112_115:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q1_112
              · by_cases h113_115:V < 114
                · have he:V = 113:=by omega
                  subst V
                  exact q1_113
                · have he:V = 114:=by omega
                  subst V
                  exact q1_114
        · by_cases h115_124:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q1_115
              · have he:V = 116:=by omega
                subst V
                exact q1_116
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q1_117
              · have he:V = 118:=by omega
                subst V
                exact q1_118
          · by_cases h119_124:V < 121
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q1_119
              · have he:V = 120:=by omega
                subst V
                exact q1_120
            · by_cases h121_124:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q1_121
              · by_cases h122_124:V < 123
                · have he:V = 122:=by omega
                  subst V
                  exact q1_122
                · have he:V = 123:=by omega
                  subst V
                  exact q1_123
      · by_cases h124_142:V < 133
        · by_cases h124_133:V < 128
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q1_124
              · have he:V = 125:=by omega
                subst V
                exact q1_125
            · by_cases h126_128:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q1_126
              · have he:V = 127:=by omega
                subst V
                exact q1_127
          · by_cases h128_133:V < 130
            · by_cases h128_130:V < 129
              · have he:V = 128:=by omega
                subst V
                exact q1_128
              · have he:V = 129:=by omega
                subst V
                exact q1_129
            · by_cases h130_133:V < 131
              · have he:V = 130:=by omega
                subst V
                exact q1_130
              · by_cases h131_133:V < 132
                · have he:V = 131:=by omega
                  subst V
                  exact q1_131
                · have he:V = 132:=by omega
                  subst V
                  exact q1_132
        · by_cases h133_142:V < 137
          · by_cases h133_137:V < 135
            · by_cases h133_135:V < 134
              · have he:V = 133:=by omega
                subst V
                exact q1_133
              · have he:V = 134:=by omega
                subst V
                exact q1_134
            · by_cases h135_137:V < 136
              · have he:V = 135:=by omega
                subst V
                exact q1_135
              · have he:V = 136:=by omega
                subst V
                exact q1_136
          · by_cases h137_142:V < 139
            · by_cases h137_139:V < 138
              · have he:V = 137:=by omega
                subst V
                exact q1_137
              · have he:V = 138:=by omega
                subst V
                exact q1_138
            · by_cases h139_142:V < 140
              · have he:V = 139:=by omega
                subst V
                exact q1_139
              · by_cases h140_142:V < 141
                · have he:V = 140:=by omega
                  subst V
                  exact q1_140
                · have he:V = 141:=by omega
                  subst V
                  exact q1_141
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
