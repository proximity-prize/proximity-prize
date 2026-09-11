import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked19

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q20_0:ThresholdAt 20 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 0 0 (by decide +kernel)
  | exact S 20 0 1 (by decide +kernel)
  | exact S 20 0 2 (by decide +kernel)
  | exact S 20 0 3 (by decide +kernel)
  | exact S 20 0 4 (by decide +kernel)
  | exact S 20 0 5 (by decide +kernel)
theorem q20_1:ThresholdAt 20 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 1 0 (by decide +kernel)
  | exact S 20 1 1 (by decide +kernel)
  | exact S 20 1 2 (by decide +kernel)
  | exact S 20 1 3 (by decide +kernel)
  | exact S 20 1 4 (by decide +kernel)
  | exact S 20 1 5 (by decide +kernel)
theorem q20_2:ThresholdAt 20 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 2 0 (by decide +kernel)
  | exact S 20 2 1 (by decide +kernel)
  | exact S 20 2 2 (by decide +kernel)
  | exact S 20 2 3 (by decide +kernel)
  | exact S 20 2 4 (by decide +kernel)
  | exact S 20 2 5 (by decide +kernel)
theorem q20_3:ThresholdAt 20 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 3 0 (by decide +kernel)
  | exact S 20 3 1 (by decide +kernel)
  | exact S 20 3 2 (by decide +kernel)
  | exact S 20 3 3 (by decide +kernel)
  | exact S 20 3 4 (by decide +kernel)
  | exact S 20 3 5 (by decide +kernel)
theorem q20_4:ThresholdAt 20 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 4 0 (by decide +kernel)
  | exact S 20 4 1 (by decide +kernel)
  | exact S 20 4 2 (by decide +kernel)
  | exact S 20 4 3 (by decide +kernel)
  | exact S 20 4 4 (by decide +kernel)
  | exact S 20 4 5 (by decide +kernel)
theorem q20_5:ThresholdAt 20 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 5 0 (by decide +kernel)
  | exact S 20 5 1 (by decide +kernel)
  | exact S 20 5 2 (by decide +kernel)
  | exact S 20 5 3 (by decide +kernel)
  | exact S 20 5 4 (by decide +kernel)
  | exact S 20 5 5 (by decide +kernel)
theorem q20_6:ThresholdAt 20 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 6 0 (by decide +kernel)
  | exact S 20 6 1 (by decide +kernel)
  | exact S 20 6 2 (by decide +kernel)
  | exact S 20 6 3 (by decide +kernel)
  | exact S 20 6 4 (by decide +kernel)
  | exact S 20 6 5 (by decide +kernel)
theorem q20_7:ThresholdAt 20 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 7 0 (by decide +kernel)
  | exact S 20 7 1 (by decide +kernel)
  | exact S 20 7 2 (by decide +kernel)
  | exact S 20 7 3 (by decide +kernel)
  | exact S 20 7 4 (by decide +kernel)
  | exact S 20 7 5 (by decide +kernel)
theorem q20_8:ThresholdAt 20 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 8 0 (by decide +kernel)
  | exact S 20 8 1 (by decide +kernel)
  | exact S 20 8 2 (by decide +kernel)
  | exact S 20 8 3 (by decide +kernel)
  | exact S 20 8 4 (by decide +kernel)
  | exact S 20 8 5 (by decide +kernel)
theorem q20_9:ThresholdAt 20 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 9 0 (by decide +kernel)
  | exact S 20 9 1 (by decide +kernel)
  | exact S 20 9 2 (by decide +kernel)
  | exact S 20 9 3 (by decide +kernel)
  | exact S 20 9 4 (by decide +kernel)
  | exact S 20 9 5 (by decide +kernel)
theorem q20_10:ThresholdAt 20 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 10 0 (by decide +kernel)
  | exact S 20 10 1 (by decide +kernel)
  | exact S 20 10 2 (by decide +kernel)
  | exact S 20 10 3 (by decide +kernel)
  | exact S 20 10 4 (by decide +kernel)
  | exact S 20 10 5 (by decide +kernel)
theorem q20_11:ThresholdAt 20 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 11 0 (by decide +kernel)
  | exact S 20 11 1 (by decide +kernel)
  | exact S 20 11 2 (by decide +kernel)
  | exact S 20 11 3 (by decide +kernel)
  | exact S 20 11 4 (by decide +kernel)
  | exact S 20 11 5 (by decide +kernel)
theorem q20_12:ThresholdAt 20 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 12 0 (by decide +kernel)
  | exact S 20 12 1 (by decide +kernel)
  | exact S 20 12 2 (by decide +kernel)
  | exact S 20 12 3 (by decide +kernel)
  | exact S 20 12 4 (by decide +kernel)
  | exact S 20 12 5 (by decide +kernel)
theorem q20_13:ThresholdAt 20 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 13 0 (by decide +kernel)
  | exact S 20 13 1 (by decide +kernel)
  | exact S 20 13 2 (by decide +kernel)
  | exact S 20 13 3 (by decide +kernel)
  | exact S 20 13 4 (by decide +kernel)
  | exact S 20 13 5 (by decide +kernel)
theorem q20_14:ThresholdAt 20 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 14 0 (by decide +kernel)
  | exact S 20 14 1 (by decide +kernel)
  | exact S 20 14 2 (by decide +kernel)
  | exact S 20 14 3 (by decide +kernel)
  | exact S 20 14 4 (by decide +kernel)
  | exact S 20 14 5 (by decide +kernel)
theorem q20_15:ThresholdAt 20 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 15 0 (by decide +kernel)
  | exact S 20 15 1 (by decide +kernel)
  | exact S 20 15 2 (by decide +kernel)
  | exact S 20 15 3 (by decide +kernel)
  | exact S 20 15 4 (by decide +kernel)
  | exact S 20 15 5 (by decide +kernel)
theorem q20_16:ThresholdAt 20 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 16 0 (by decide +kernel)
  | exact S 20 16 1 (by decide +kernel)
  | exact S 20 16 2 (by decide +kernel)
  | exact S 20 16 3 (by decide +kernel)
  | exact S 20 16 4 (by decide +kernel)
  | exact S 20 16 5 (by decide +kernel)
theorem q20_17:ThresholdAt 20 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 17 0 (by decide +kernel)
  | exact S 20 17 1 (by decide +kernel)
  | exact S 20 17 2 (by decide +kernel)
  | exact S 20 17 3 (by decide +kernel)
  | exact S 20 17 4 (by decide +kernel)
  | exact S 20 17 5 (by decide +kernel)
theorem q20_18:ThresholdAt 20 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 18 0 (by decide +kernel)
  | exact S 20 18 1 (by decide +kernel)
  | exact S 20 18 2 (by decide +kernel)
  | exact S 20 18 3 (by decide +kernel)
  | exact S 20 18 4 (by decide +kernel)
  | exact S 20 18 5 (by decide +kernel)
theorem q20_19:ThresholdAt 20 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 19 0 (by decide +kernel)
  | exact S 20 19 1 (by decide +kernel)
  | exact S 20 19 2 (by decide +kernel)
  | exact S 20 19 3 (by decide +kernel)
  | exact S 20 19 4 (by decide +kernel)
  | exact S 20 19 5 (by decide +kernel)
theorem q20_20:ThresholdAt 20 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 20 0 (by decide +kernel)
  | exact S 20 20 1 (by decide +kernel)
  | exact S 20 20 2 (by decide +kernel)
  | exact S 20 20 3 (by decide +kernel)
  | exact S 20 20 4 (by decide +kernel)
  | exact S 20 20 5 (by decide +kernel)
theorem q20_21:ThresholdAt 20 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 21 0 (by decide +kernel)
  | exact S 20 21 1 (by decide +kernel)
  | exact S 20 21 2 (by decide +kernel)
  | exact S 20 21 3 (by decide +kernel)
  | exact S 20 21 4 (by decide +kernel)
  | exact S 20 21 5 (by decide +kernel)
theorem q20_22:ThresholdAt 20 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 22 0 (by decide +kernel)
  | exact S 20 22 1 (by decide +kernel)
  | exact S 20 22 2 (by decide +kernel)
  | exact S 20 22 3 (by decide +kernel)
  | exact S 20 22 4 (by decide +kernel)
  | exact S 20 22 5 (by decide +kernel)
theorem q20_23:ThresholdAt 20 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 23 0 (by decide +kernel)
  | exact S 20 23 1 (by decide +kernel)
  | exact S 20 23 2 (by decide +kernel)
  | exact S 20 23 3 (by decide +kernel)
  | exact S 20 23 4 (by decide +kernel)
  | exact S 20 23 5 (by decide +kernel)
theorem q20_24:ThresholdAt 20 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 24 0 (by decide +kernel)
  | exact S 20 24 1 (by decide +kernel)
  | exact S 20 24 2 (by decide +kernel)
  | exact S 20 24 3 (by decide +kernel)
  | exact S 20 24 4 (by decide +kernel)
  | exact S 20 24 5 (by decide +kernel)
theorem q20_25:ThresholdAt 20 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 25 0 (by decide +kernel)
  | exact S 20 25 1 (by decide +kernel)
  | exact S 20 25 2 (by decide +kernel)
  | exact S 20 25 3 (by decide +kernel)
  | exact S 20 25 4 (by decide +kernel)
  | exact S 20 25 5 (by decide +kernel)
theorem q20_26:ThresholdAt 20 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 26 0 (by decide +kernel)
  | exact S 20 26 1 (by decide +kernel)
  | exact S 20 26 2 (by decide +kernel)
  | exact S 20 26 3 (by decide +kernel)
  | exact S 20 26 4 (by decide +kernel)
  | exact S 20 26 5 (by decide +kernel)
theorem q20_27:ThresholdAt 20 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 27 0 (by decide +kernel)
  | exact S 20 27 1 (by decide +kernel)
  | exact S 20 27 2 (by decide +kernel)
  | exact S 20 27 3 (by decide +kernel)
  | exact S 20 27 4 (by decide +kernel)
  | exact S 20 27 5 (by decide +kernel)
theorem q20_28:ThresholdAt 20 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 28 0 (by decide +kernel)
  | exact S 20 28 1 (by decide +kernel)
  | exact S 20 28 2 (by decide +kernel)
  | exact S 20 28 3 (by decide +kernel)
  | exact S 20 28 4 (by decide +kernel)
  | exact S 20 28 5 (by decide +kernel)
theorem q20_29:ThresholdAt 20 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 29 0 (by decide +kernel)
  | exact S 20 29 1 (by decide +kernel)
  | exact S 20 29 2 (by decide +kernel)
  | exact S 20 29 3 (by decide +kernel)
  | exact S 20 29 4 (by decide +kernel)
  | exact S 20 29 5 (by decide +kernel)
theorem q20_30:ThresholdAt 20 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 30 0 (by decide +kernel)
  | exact S 20 30 1 (by decide +kernel)
  | exact S 20 30 2 (by decide +kernel)
  | exact S 20 30 3 (by decide +kernel)
  | exact S 20 30 4 (by decide +kernel)
  | exact S 20 30 5 (by decide +kernel)
theorem q20_31:ThresholdAt 20 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 31 0 (by decide +kernel)
  | exact S 20 31 1 (by decide +kernel)
  | exact S 20 31 2 (by decide +kernel)
  | exact S 20 31 3 (by decide +kernel)
  | exact S 20 31 4 (by decide +kernel)
  | exact S 20 31 5 (by decide +kernel)
theorem q20_32:ThresholdAt 20 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 32 0 (by decide +kernel)
  | exact S 20 32 1 (by decide +kernel)
  | exact S 20 32 2 (by decide +kernel)
  | exact S 20 32 3 (by decide +kernel)
  | exact S 20 32 4 (by decide +kernel)
  | exact S 20 32 5 (by decide +kernel)
theorem q20_33:ThresholdAt 20 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 33 0 (by decide +kernel)
  | exact S 20 33 1 (by decide +kernel)
  | exact S 20 33 2 (by decide +kernel)
  | exact S 20 33 3 (by decide +kernel)
  | exact S 20 33 4 (by decide +kernel)
  | exact S 20 33 5 (by decide +kernel)
theorem q20_34:ThresholdAt 20 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 34 0 (by decide +kernel)
  | exact S 20 34 1 (by decide +kernel)
  | exact S 20 34 2 (by decide +kernel)
  | exact S 20 34 3 (by decide +kernel)
  | exact S 20 34 4 (by decide +kernel)
  | exact S 20 34 5 (by decide +kernel)
theorem q20_35:ThresholdAt 20 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 35 0 (by decide +kernel)
  | exact S 20 35 1 (by decide +kernel)
  | exact S 20 35 2 (by decide +kernel)
  | exact S 20 35 3 (by decide +kernel)
  | exact S 20 35 4 (by decide +kernel)
  | exact S 20 35 5 (by decide +kernel)
theorem q20_36:ThresholdAt 20 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 36 0 (by decide +kernel)
  | exact S 20 36 1 (by decide +kernel)
  | exact S 20 36 2 (by decide +kernel)
  | exact S 20 36 3 (by decide +kernel)
  | exact S 20 36 4 (by decide +kernel)
  | exact S 20 36 5 (by decide +kernel)
theorem q20_37:ThresholdAt 20 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 37 0 (by decide +kernel)
  | exact S 20 37 1 (by decide +kernel)
  | exact S 20 37 2 (by decide +kernel)
  | exact S 20 37 3 (by decide +kernel)
  | exact S 20 37 4 (by decide +kernel)
  | exact S 20 37 5 (by decide +kernel)
theorem q20_38:ThresholdAt 20 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 38 0 (by decide +kernel)
  | exact S 20 38 1 (by decide +kernel)
  | exact S 20 38 2 (by decide +kernel)
  | exact S 20 38 3 (by decide +kernel)
  | exact S 20 38 4 (by decide +kernel)
  | exact S 20 38 5 (by decide +kernel)
theorem q20_39:ThresholdAt 20 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 39 0 (by decide +kernel)
  | exact S 20 39 1 (by decide +kernel)
  | exact S 20 39 2 (by decide +kernel)
  | exact S 20 39 3 (by decide +kernel)
  | exact S 20 39 4 (by decide +kernel)
  | exact S 20 39 5 (by decide +kernel)
theorem q20_40:ThresholdAt 20 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 40 0 (by decide +kernel)
  | exact S 20 40 1 (by decide +kernel)
  | exact S 20 40 2 (by decide +kernel)
  | exact S 20 40 3 (by decide +kernel)
  | exact S 20 40 4 (by decide +kernel)
  | exact S 20 40 5 (by decide +kernel)
theorem q20_41:ThresholdAt 20 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 41 0 (by decide +kernel)
  | exact S 20 41 1 (by decide +kernel)
  | exact S 20 41 2 (by decide +kernel)
  | exact S 20 41 3 (by decide +kernel)
  | exact S 20 41 4 (by decide +kernel)
  | exact S 20 41 5 (by decide +kernel)
theorem q20_42:ThresholdAt 20 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 42 0 (by decide +kernel)
  | exact S 20 42 1 (by decide +kernel)
  | exact S 20 42 2 (by decide +kernel)
  | exact S 20 42 3 (by decide +kernel)
  | exact S 20 42 4 (by decide +kernel)
  | exact S 20 42 5 (by decide +kernel)
theorem q20_43:ThresholdAt 20 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 43 0 (by decide +kernel)
  | exact S 20 43 1 (by decide +kernel)
  | exact S 20 43 2 (by decide +kernel)
  | exact S 20 43 3 (by decide +kernel)
  | exact S 20 43 4 (by decide +kernel)
  | exact S 20 43 5 (by decide +kernel)
theorem q20_44:ThresholdAt 20 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 44 0 (by decide +kernel)
  | exact S 20 44 1 (by decide +kernel)
  | exact S 20 44 2 (by decide +kernel)
  | exact S 20 44 3 (by decide +kernel)
  | exact S 20 44 4 (by decide +kernel)
  | exact S 20 44 5 (by decide +kernel)
theorem q20_45:ThresholdAt 20 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 45 0 (by decide +kernel)
  | exact S 20 45 1 (by decide +kernel)
  | exact S 20 45 2 (by decide +kernel)
  | exact S 20 45 3 (by decide +kernel)
  | exact S 20 45 4 (by decide +kernel)
  | exact S 20 45 5 (by decide +kernel)
theorem q20_46:ThresholdAt 20 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 46 0 (by decide +kernel)
  | exact S 20 46 1 (by decide +kernel)
  | exact S 20 46 2 (by decide +kernel)
  | exact S 20 46 3 (by decide +kernel)
  | exact S 20 46 4 (by decide +kernel)
  | exact S 20 46 5 (by decide +kernel)
theorem q20_47:ThresholdAt 20 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 47 0 (by decide +kernel)
  | exact S 20 47 1 (by decide +kernel)
  | exact S 20 47 2 (by decide +kernel)
  | exact S 20 47 3 (by decide +kernel)
  | exact S 20 47 4 (by decide +kernel)
  | exact S 20 47 5 (by decide +kernel)
theorem q20_48:ThresholdAt 20 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 48 0 (by decide +kernel)
  | exact S 20 48 1 (by decide +kernel)
  | exact S 20 48 2 (by decide +kernel)
  | exact S 20 48 3 (by decide +kernel)
  | exact S 20 48 4 (by decide +kernel)
  | exact S 20 48 5 (by decide +kernel)
theorem q20_49:ThresholdAt 20 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 49 0 (by decide +kernel)
  | exact S 20 49 1 (by decide +kernel)
  | exact S 20 49 2 (by decide +kernel)
  | exact S 20 49 3 (by decide +kernel)
  | exact S 20 49 4 (by decide +kernel)
  | exact S 20 49 5 (by decide +kernel)
theorem q20_50:ThresholdAt 20 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 50 0 (by decide +kernel)
  | exact S 20 50 1 (by decide +kernel)
  | exact S 20 50 2 (by decide +kernel)
  | exact S 20 50 3 (by decide +kernel)
  | exact S 20 50 4 (by decide +kernel)
  | exact S 20 50 5 (by decide +kernel)
theorem q20_51:ThresholdAt 20 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 51 0 (by decide +kernel)
  | exact S 20 51 1 (by decide +kernel)
  | exact S 20 51 2 (by decide +kernel)
  | exact S 20 51 3 (by decide +kernel)
  | exact S 20 51 4 (by decide +kernel)
  | exact S 20 51 5 (by decide +kernel)
theorem q20_52:ThresholdAt 20 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 52 0 (by decide +kernel)
  | exact S 20 52 1 (by decide +kernel)
  | exact S 20 52 2 (by decide +kernel)
  | exact S 20 52 3 (by decide +kernel)
  | exact S 20 52 4 (by decide +kernel)
  | exact S 20 52 5 (by decide +kernel)
theorem q20_53:ThresholdAt 20 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 53 0 (by decide +kernel)
  | exact S 20 53 1 (by decide +kernel)
  | exact S 20 53 2 (by decide +kernel)
  | exact S 20 53 3 (by decide +kernel)
  | exact S 20 53 4 (by decide +kernel)
  | exact S 20 53 5 (by decide +kernel)
theorem q20_54:ThresholdAt 20 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 54 0 (by decide +kernel)
  | exact S 20 54 1 (by decide +kernel)
  | exact S 20 54 2 (by decide +kernel)
  | exact S 20 54 3 (by decide +kernel)
  | exact S 20 54 4 (by decide +kernel)
  | exact S 20 54 5 (by decide +kernel)
theorem q20_55:ThresholdAt 20 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 55 0 (by decide +kernel)
  | exact S 20 55 1 (by decide +kernel)
  | exact S 20 55 2 (by decide +kernel)
  | exact S 20 55 3 (by decide +kernel)
  | exact S 20 55 4 (by decide +kernel)
  | exact S 20 55 5 (by decide +kernel)
theorem q20_56:ThresholdAt 20 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 56 0 (by decide +kernel)
  | exact S 20 56 1 (by decide +kernel)
  | exact S 20 56 2 (by decide +kernel)
  | exact S 20 56 3 (by decide +kernel)
  | exact S 20 56 4 (by decide +kernel)
  | exact S 20 56 5 (by decide +kernel)
theorem q20_57:ThresholdAt 20 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 57 0 (by decide +kernel)
  | exact S 20 57 1 (by decide +kernel)
  | exact S 20 57 2 (by decide +kernel)
  | exact S 20 57 3 (by decide +kernel)
  | exact S 20 57 4 (by decide +kernel)
  | exact S 20 57 5 (by decide +kernel)
theorem q20_58:ThresholdAt 20 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 58 0 (by decide +kernel)
  | exact S 20 58 1 (by decide +kernel)
  | exact S 20 58 2 (by decide +kernel)
  | exact S 20 58 3 (by decide +kernel)
  | exact S 20 58 4 (by decide +kernel)
  | exact S 20 58 5 (by decide +kernel)
theorem q20_59:ThresholdAt 20 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 59 0 (by decide +kernel)
  | exact S 20 59 1 (by decide +kernel)
  | exact S 20 59 2 (by decide +kernel)
  | exact S 20 59 3 (by decide +kernel)
  | exact S 20 59 4 (by decide +kernel)
  | exact S 20 59 5 (by decide +kernel)
theorem q20_60:ThresholdAt 20 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 60 0 (by decide +kernel)
  | exact S 20 60 1 (by decide +kernel)
  | exact S 20 60 2 (by decide +kernel)
  | exact S 20 60 3 (by decide +kernel)
  | exact S 20 60 4 (by decide +kernel)
  | exact S 20 60 5 (by decide +kernel)
theorem q20_61:ThresholdAt 20 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 61 0 (by decide +kernel)
  | exact S 20 61 1 (by decide +kernel)
  | exact S 20 61 2 (by decide +kernel)
  | exact S 20 61 3 (by decide +kernel)
  | exact S 20 61 4 (by decide +kernel)
  | exact S 20 61 5 (by decide +kernel)
theorem q20_62:ThresholdAt 20 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 62 0 (by decide +kernel)
  | exact S 20 62 1 (by decide +kernel)
  | exact S 20 62 2 (by decide +kernel)
  | exact S 20 62 3 (by decide +kernel)
  | exact S 20 62 4 (by decide +kernel)
  | exact S 20 62 5 (by decide +kernel)
theorem q20_63:ThresholdAt 20 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 63 0 (by decide +kernel)
  | exact S 20 63 1 (by decide +kernel)
  | exact S 20 63 2 (by decide +kernel)
  | exact S 20 63 3 (by decide +kernel)
  | exact S 20 63 4 (by decide +kernel)
  | exact S 20 63 5 (by decide +kernel)
theorem q20_64:ThresholdAt 20 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 64 0 (by decide +kernel)
  | exact S 20 64 1 (by decide +kernel)
  | exact S 20 64 2 (by decide +kernel)
  | exact S 20 64 3 (by decide +kernel)
  | exact S 20 64 4 (by decide +kernel)
  | exact S 20 64 5 (by decide +kernel)
theorem q20_65:ThresholdAt 20 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 65 0 (by decide +kernel)
  | exact S 20 65 1 (by decide +kernel)
  | exact S 20 65 2 (by decide +kernel)
  | exact S 20 65 3 (by decide +kernel)
  | exact S 20 65 4 (by decide +kernel)
  | exact S 20 65 5 (by decide +kernel)
theorem q20_66:ThresholdAt 20 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 66 0 (by decide +kernel)
  | exact S 20 66 1 (by decide +kernel)
  | exact S 20 66 2 (by decide +kernel)
  | exact S 20 66 3 (by decide +kernel)
  | exact S 20 66 4 (by decide +kernel)
  | exact S 20 66 5 (by decide +kernel)
theorem q20_67:ThresholdAt 20 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 67 0 (by decide +kernel)
  | exact S 20 67 1 (by decide +kernel)
  | exact S 20 67 2 (by decide +kernel)
  | exact S 20 67 3 (by decide +kernel)
  | exact S 20 67 4 (by decide +kernel)
  | exact S 20 67 5 (by decide +kernel)
theorem q20_68:ThresholdAt 20 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 68 0 (by decide +kernel)
  | exact S 20 68 1 (by decide +kernel)
  | exact S 20 68 2 (by decide +kernel)
  | exact S 20 68 3 (by decide +kernel)
  | exact S 20 68 4 (by decide +kernel)
  | exact S 20 68 5 (by decide +kernel)
theorem q20_69:ThresholdAt 20 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 69 0 (by decide +kernel)
  | exact S 20 69 1 (by decide +kernel)
  | exact S 20 69 2 (by decide +kernel)
  | exact S 20 69 3 (by decide +kernel)
  | exact S 20 69 4 (by decide +kernel)
  | exact S 20 69 5 (by decide +kernel)
theorem q20_70:ThresholdAt 20 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 70 0 (by decide +kernel)
  | exact S 20 70 1 (by decide +kernel)
  | exact S 20 70 2 (by decide +kernel)
  | exact S 20 70 3 (by decide +kernel)
  | exact S 20 70 4 (by decide +kernel)
  | exact S 20 70 5 (by decide +kernel)
theorem q20_71:ThresholdAt 20 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 71 0 (by decide +kernel)
  | exact S 20 71 1 (by decide +kernel)
  | exact S 20 71 2 (by decide +kernel)
  | exact S 20 71 3 (by decide +kernel)
  | exact S 20 71 4 (by decide +kernel)
  | exact S 20 71 5 (by decide +kernel)
theorem q20_72:ThresholdAt 20 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 72 0 (by decide +kernel)
  | exact S 20 72 1 (by decide +kernel)
  | exact S 20 72 2 (by decide +kernel)
  | exact S 20 72 3 (by decide +kernel)
  | exact S 20 72 4 (by decide +kernel)
  | exact S 20 72 5 (by decide +kernel)
theorem q20_73:ThresholdAt 20 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 73 0 (by decide +kernel)
  | exact S 20 73 1 (by decide +kernel)
  | exact S 20 73 2 (by decide +kernel)
  | exact S 20 73 3 (by decide +kernel)
  | exact S 20 73 4 (by decide +kernel)
  | exact S 20 73 5 (by decide +kernel)
theorem q20_74:ThresholdAt 20 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 74 0 (by decide +kernel)
  | exact S 20 74 1 (by decide +kernel)
  | exact S 20 74 2 (by decide +kernel)
  | exact S 20 74 3 (by decide +kernel)
  | exact S 20 74 4 (by decide +kernel)
  | exact S 20 74 5 (by decide +kernel)
theorem q20_75:ThresholdAt 20 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 75 0 (by decide +kernel)
  | exact S 20 75 1 (by decide +kernel)
  | exact S 20 75 2 (by decide +kernel)
  | exact S 20 75 3 (by decide +kernel)
  | exact S 20 75 4 (by decide +kernel)
  | exact S 20 75 5 (by decide +kernel)
theorem q20_76:ThresholdAt 20 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 76 0 (by decide +kernel)
  | exact S 20 76 1 (by decide +kernel)
  | exact S 20 76 2 (by decide +kernel)
  | exact S 20 76 3 (by decide +kernel)
  | exact S 20 76 4 (by decide +kernel)
  | exact S 20 76 5 (by decide +kernel)
theorem q20_77:ThresholdAt 20 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 77 0 (by decide +kernel)
  | exact S 20 77 1 (by decide +kernel)
  | exact S 20 77 2 (by decide +kernel)
  | exact S 20 77 3 (by decide +kernel)
  | exact S 20 77 4 (by decide +kernel)
  | exact S 20 77 5 (by decide +kernel)
theorem q20_78:ThresholdAt 20 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 78 0 (by decide +kernel)
  | exact S 20 78 1 (by decide +kernel)
  | exact S 20 78 2 (by decide +kernel)
  | exact S 20 78 3 (by decide +kernel)
  | exact S 20 78 4 (by decide +kernel)
  | exact S 20 78 5 (by decide +kernel)
theorem q20_79:ThresholdAt 20 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 79 0 (by decide +kernel)
  | exact S 20 79 1 (by decide +kernel)
  | exact S 20 79 2 (by decide +kernel)
  | exact S 20 79 3 (by decide +kernel)
  | exact S 20 79 4 (by decide +kernel)
  | exact S 20 79 5 (by decide +kernel)
theorem q20_80:ThresholdAt 20 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 80 0 (by decide +kernel)
  | exact S 20 80 1 (by decide +kernel)
  | exact S 20 80 2 (by decide +kernel)
  | exact S 20 80 3 (by decide +kernel)
  | exact S 20 80 4 (by decide +kernel)
  | exact S 20 80 5 (by decide +kernel)
theorem q20_81:ThresholdAt 20 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 81 0 (by decide +kernel)
  | exact S 20 81 1 (by decide +kernel)
  | exact S 20 81 2 (by decide +kernel)
  | exact S 20 81 3 (by decide +kernel)
  | exact S 20 81 4 (by decide +kernel)
  | exact S 20 81 5 (by decide +kernel)
theorem q20_82:ThresholdAt 20 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 82 0 (by decide +kernel)
  | exact S 20 82 1 (by decide +kernel)
  | exact S 20 82 2 (by decide +kernel)
  | exact S 20 82 3 (by decide +kernel)
  | exact S 20 82 4 (by decide +kernel)
  | exact S 20 82 5 (by decide +kernel)
theorem q20_83:ThresholdAt 20 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 83 0 (by decide +kernel)
  | exact S 20 83 1 (by decide +kernel)
  | exact S 20 83 2 (by decide +kernel)
  | exact S 20 83 3 (by decide +kernel)
  | exact S 20 83 4 (by decide +kernel)
  | exact S 20 83 5 (by decide +kernel)
theorem q20_84:ThresholdAt 20 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 84 0 (by decide +kernel)
  | exact S 20 84 1 (by decide +kernel)
  | exact S 20 84 2 (by decide +kernel)
  | exact S 20 84 3 (by decide +kernel)
  | exact S 20 84 4 (by decide +kernel)
  | exact S 20 84 5 (by decide +kernel)
theorem q20_85:ThresholdAt 20 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 85 0 (by decide +kernel)
  | exact S 20 85 1 (by decide +kernel)
  | exact S 20 85 2 (by decide +kernel)
  | exact S 20 85 3 (by decide +kernel)
  | exact S 20 85 4 (by decide +kernel)
  | exact S 20 85 5 (by decide +kernel)
theorem q20_86:ThresholdAt 20 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 86 0 (by decide +kernel)
  | exact S 20 86 1 (by decide +kernel)
  | exact S 20 86 2 (by decide +kernel)
  | exact S 20 86 3 (by decide +kernel)
  | exact S 20 86 4 (by decide +kernel)
  | exact S 20 86 5 (by decide +kernel)
theorem q20_87:ThresholdAt 20 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 87 0 (by decide +kernel)
  | exact S 20 87 1 (by decide +kernel)
  | exact S 20 87 2 (by decide +kernel)
  | exact S 20 87 3 (by decide +kernel)
  | exact S 20 87 4 (by decide +kernel)
  | exact S 20 87 5 (by decide +kernel)
theorem q20_88:ThresholdAt 20 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 88 0 (by decide +kernel)
  | exact S 20 88 1 (by decide +kernel)
  | exact S 20 88 2 (by decide +kernel)
  | exact S 20 88 3 (by decide +kernel)
  | exact S 20 88 4 (by decide +kernel)
  | exact S 20 88 5 (by decide +kernel)
theorem q20_89:ThresholdAt 20 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 89 0 (by decide +kernel)
  | exact S 20 89 1 (by decide +kernel)
  | exact S 20 89 2 (by decide +kernel)
  | exact S 20 89 3 (by decide +kernel)
  | exact S 20 89 4 (by decide +kernel)
  | exact S 20 89 5 (by decide +kernel)
theorem q20_90:ThresholdAt 20 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 90 0 (by decide +kernel)
  | exact S 20 90 1 (by decide +kernel)
  | exact S 20 90 2 (by decide +kernel)
  | exact S 20 90 3 (by decide +kernel)
  | exact S 20 90 4 (by decide +kernel)
  | exact S 20 90 5 (by decide +kernel)
theorem q20_91:ThresholdAt 20 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 91 0 (by decide +kernel)
  | exact S 20 91 1 (by decide +kernel)
  | exact S 20 91 2 (by decide +kernel)
  | exact S 20 91 3 (by decide +kernel)
  | exact S 20 91 4 (by decide +kernel)
  | exact S 20 91 5 (by decide +kernel)
theorem q20_92:ThresholdAt 20 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 92 0 (by decide +kernel)
  | exact S 20 92 1 (by decide +kernel)
  | exact S 20 92 2 (by decide +kernel)
  | exact S 20 92 3 (by decide +kernel)
  | exact S 20 92 4 (by decide +kernel)
  | exact S 20 92 5 (by decide +kernel)
theorem q20_93:ThresholdAt 20 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 93 0 (by decide +kernel)
  | exact S 20 93 1 (by decide +kernel)
  | exact S 20 93 2 (by decide +kernel)
  | exact S 20 93 3 (by decide +kernel)
  | exact S 20 93 4 (by decide +kernel)
  | exact S 20 93 5 (by decide +kernel)
theorem q20_94:ThresholdAt 20 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 94 0 (by decide +kernel)
  | exact S 20 94 1 (by decide +kernel)
  | exact S 20 94 2 (by decide +kernel)
  | exact S 20 94 3 (by decide +kernel)
  | exact S 20 94 4 (by decide +kernel)
  | exact S 20 94 5 (by decide +kernel)
theorem q20_95:ThresholdAt 20 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 95 0 (by decide +kernel)
  | exact S 20 95 1 (by decide +kernel)
  | exact S 20 95 2 (by decide +kernel)
  | exact S 20 95 3 (by decide +kernel)
  | exact S 20 95 4 (by decide +kernel)
  | exact S 20 95 5 (by decide +kernel)
theorem q20_96:ThresholdAt 20 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 96 0 (by decide +kernel)
  | exact S 20 96 1 (by decide +kernel)
  | exact S 20 96 2 (by decide +kernel)
  | exact S 20 96 3 (by decide +kernel)
  | exact S 20 96 4 (by decide +kernel)
  | exact S 20 96 5 (by decide +kernel)
theorem q20_97:ThresholdAt 20 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 97 0 (by decide +kernel)
  | exact S 20 97 1 (by decide +kernel)
  | exact S 20 97 2 (by decide +kernel)
  | exact S 20 97 3 (by decide +kernel)
  | exact S 20 97 4 (by decide +kernel)
  | exact S 20 97 5 (by decide +kernel)
theorem q20_98:ThresholdAt 20 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 98 0 (by decide +kernel)
  | exact S 20 98 1 (by decide +kernel)
  | exact S 20 98 2 (by decide +kernel)
  | exact S 20 98 3 (by decide +kernel)
  | exact S 20 98 4 (by decide +kernel)
  | exact S 20 98 5 (by decide +kernel)
theorem q20_99:ThresholdAt 20 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 99 0 (by decide +kernel)
  | exact S 20 99 1 (by decide +kernel)
  | exact S 20 99 2 (by decide +kernel)
  | exact S 20 99 3 (by decide +kernel)
  | exact S 20 99 4 (by decide +kernel)
  | exact S 20 99 5 (by decide +kernel)
theorem q20_100:ThresholdAt 20 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 100 0 (by decide +kernel)
  | exact S 20 100 1 (by decide +kernel)
  | exact S 20 100 2 (by decide +kernel)
  | exact S 20 100 3 (by decide +kernel)
  | exact S 20 100 4 (by decide +kernel)
  | exact S 20 100 5 (by decide +kernel)
theorem q20_101:ThresholdAt 20 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 101 0 (by decide +kernel)
  | exact S 20 101 1 (by decide +kernel)
  | exact S 20 101 2 (by decide +kernel)
  | exact S 20 101 3 (by decide +kernel)
  | exact S 20 101 4 (by decide +kernel)
  | exact S 20 101 5 (by decide +kernel)
theorem q20_102:ThresholdAt 20 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 102 0 (by decide +kernel)
  | exact S 20 102 1 (by decide +kernel)
  | exact S 20 102 2 (by decide +kernel)
  | exact S 20 102 3 (by decide +kernel)
  | exact S 20 102 4 (by decide +kernel)
  | exact S 20 102 5 (by decide +kernel)
theorem q20_103:ThresholdAt 20 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 103 0 (by decide +kernel)
  | exact S 20 103 1 (by decide +kernel)
  | exact S 20 103 2 (by decide +kernel)
  | exact S 20 103 3 (by decide +kernel)
  | exact S 20 103 4 (by decide +kernel)
  | exact S 20 103 5 (by decide +kernel)
theorem q20_104:ThresholdAt 20 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 104 0 (by decide +kernel)
  | exact S 20 104 1 (by decide +kernel)
  | exact S 20 104 2 (by decide +kernel)
  | exact S 20 104 3 (by decide +kernel)
  | exact S 20 104 4 (by decide +kernel)
  | exact S 20 104 5 (by decide +kernel)
theorem q20_105:ThresholdAt 20 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 105 0 (by decide +kernel)
  | exact S 20 105 1 (by decide +kernel)
  | exact S 20 105 2 (by decide +kernel)
  | exact S 20 105 3 (by decide +kernel)
  | exact S 20 105 4 (by decide +kernel)
  | exact S 20 105 5 (by decide +kernel)
theorem q20_106:ThresholdAt 20 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 106 0 (by decide +kernel)
  | exact S 20 106 1 (by decide +kernel)
  | exact S 20 106 2 (by decide +kernel)
  | exact S 20 106 3 (by decide +kernel)
  | exact S 20 106 4 (by decide +kernel)
  | exact S 20 106 5 (by decide +kernel)
theorem q20_107:ThresholdAt 20 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 107 0 (by decide +kernel)
  | exact S 20 107 1 (by decide +kernel)
  | exact S 20 107 2 (by decide +kernel)
  | exact S 20 107 3 (by decide +kernel)
  | exact S 20 107 4 (by decide +kernel)
  | exact S 20 107 5 (by decide +kernel)
theorem q20_108:ThresholdAt 20 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 108 0 (by decide +kernel)
  | exact S 20 108 1 (by decide +kernel)
  | exact S 20 108 2 (by decide +kernel)
  | exact S 20 108 3 (by decide +kernel)
  | exact S 20 108 4 (by decide +kernel)
  | exact S 20 108 5 (by decide +kernel)
theorem q20_109:ThresholdAt 20 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 109 0 (by decide +kernel)
  | exact S 20 109 1 (by decide +kernel)
  | exact S 20 109 2 (by decide +kernel)
  | exact S 20 109 3 (by decide +kernel)
  | exact S 20 109 4 (by decide +kernel)
  | exact S 20 109 5 (by decide +kernel)
theorem q20_110:ThresholdAt 20 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 110 0 (by decide +kernel)
  | exact S 20 110 1 (by decide +kernel)
  | exact S 20 110 2 (by decide +kernel)
  | exact S 20 110 3 (by decide +kernel)
  | exact S 20 110 4 (by decide +kernel)
  | exact S 20 110 5 (by decide +kernel)
theorem q20_111:ThresholdAt 20 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 111 0 (by decide +kernel)
  | exact S 20 111 1 (by decide +kernel)
  | exact S 20 111 2 (by decide +kernel)
  | exact S 20 111 3 (by decide +kernel)
  | exact S 20 111 4 (by decide +kernel)
  | exact S 20 111 5 (by decide +kernel)
theorem q20_112:ThresholdAt 20 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 112 0 (by decide +kernel)
  | exact S 20 112 1 (by decide +kernel)
  | exact S 20 112 2 (by decide +kernel)
  | exact S 20 112 3 (by decide +kernel)
  | exact S 20 112 4 (by decide +kernel)
  | exact S 20 112 5 (by decide +kernel)
theorem q20_113:ThresholdAt 20 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 113 0 (by decide +kernel)
  | exact S 20 113 1 (by decide +kernel)
  | exact S 20 113 2 (by decide +kernel)
  | exact S 20 113 3 (by decide +kernel)
  | exact S 20 113 4 (by decide +kernel)
  | exact S 20 113 5 (by decide +kernel)
theorem q20_114:ThresholdAt 20 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 114 0 (by decide +kernel)
  | exact S 20 114 1 (by decide +kernel)
  | exact S 20 114 2 (by decide +kernel)
  | exact S 20 114 3 (by decide +kernel)
  | exact S 20 114 4 (by decide +kernel)
  | exact S 20 114 5 (by decide +kernel)
theorem q20_115:ThresholdAt 20 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 115 0 (by decide +kernel)
  | exact S 20 115 1 (by decide +kernel)
  | exact S 20 115 2 (by decide +kernel)
  | exact S 20 115 3 (by decide +kernel)
  | exact S 20 115 4 (by decide +kernel)
  | exact S 20 115 5 (by decide +kernel)
theorem q20_116:ThresholdAt 20 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 116 0 (by decide +kernel)
  | exact S 20 116 1 (by decide +kernel)
  | exact S 20 116 2 (by decide +kernel)
  | exact S 20 116 3 (by decide +kernel)
  | exact S 20 116 4 (by decide +kernel)
  | exact S 20 116 5 (by decide +kernel)
theorem q20_117:ThresholdAt 20 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 117 0 (by decide +kernel)
  | exact S 20 117 1 (by decide +kernel)
  | exact S 20 117 2 (by decide +kernel)
  | exact S 20 117 3 (by decide +kernel)
  | exact S 20 117 4 (by decide +kernel)
  | exact S 20 117 5 (by decide +kernel)
theorem q20_118:ThresholdAt 20 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 118 0 (by decide +kernel)
  | exact S 20 118 1 (by decide +kernel)
  | exact S 20 118 2 (by decide +kernel)
  | exact S 20 118 3 (by decide +kernel)
  | exact S 20 118 4 (by decide +kernel)
  | exact S 20 118 5 (by decide +kernel)
theorem q20_119:ThresholdAt 20 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 119 0 (by decide +kernel)
  | exact S 20 119 1 (by decide +kernel)
  | exact S 20 119 2 (by decide +kernel)
  | exact S 20 119 3 (by decide +kernel)
  | exact S 20 119 4 (by decide +kernel)
  | exact S 20 119 5 (by decide +kernel)
theorem q20_120:ThresholdAt 20 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 120 0 (by decide +kernel)
  | exact S 20 120 1 (by decide +kernel)
  | exact S 20 120 2 (by decide +kernel)
  | exact S 20 120 3 (by decide +kernel)
  | exact S 20 120 4 (by decide +kernel)
  | exact S 20 120 5 (by decide +kernel)
theorem q20_121:ThresholdAt 20 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 121 0 (by decide +kernel)
  | exact S 20 121 1 (by decide +kernel)
  | exact S 20 121 2 (by decide +kernel)
  | exact S 20 121 3 (by decide +kernel)
  | exact S 20 121 4 (by decide +kernel)
  | exact S 20 121 5 (by decide +kernel)
theorem q20_122:ThresholdAt 20 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 122 0 (by decide +kernel)
  | exact S 20 122 1 (by decide +kernel)
  | exact S 20 122 2 (by decide +kernel)
  | exact S 20 122 3 (by decide +kernel)
  | exact S 20 122 4 (by decide +kernel)
  | exact S 20 122 5 (by decide +kernel)
theorem checkedR20:∀ V ∈ List.range 123,ThresholdAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0_123:V < 61
  · by_cases h0_61:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q20_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q20_1
              · have he:V = 2:=by omega
                subst V
                exact q20_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q20_3
              · have he:V = 4:=by omega
                subst V
                exact q20_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q20_5
              · have he:V = 6:=by omega
                subst V
                exact q20_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q20_7
              · have he:V = 8:=by omega
                subst V
                exact q20_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q20_9
              · have he:V = 10:=by omega
                subst V
                exact q20_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q20_11
              · have he:V = 12:=by omega
                subst V
                exact q20_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q20_13
              · have he:V = 14:=by omega
                subst V
                exact q20_14
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have he:V = 15:=by omega
              subst V
              exact q20_15
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q20_16
              · have he:V = 17:=by omega
                subst V
                exact q20_17
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q20_18
              · have he:V = 19:=by omega
                subst V
                exact q20_19
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q20_20
              · have he:V = 21:=by omega
                subst V
                exact q20_21
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q20_22
              · have he:V = 23:=by omega
                subst V
                exact q20_23
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q20_24
              · have he:V = 25:=by omega
                subst V
                exact q20_25
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q20_26
              · have he:V = 27:=by omega
                subst V
                exact q20_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q20_28
              · have he:V = 29:=by omega
                subst V
                exact q20_29
    · by_cases h30_61:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have he:V = 30:=by omega
              subst V
              exact q20_30
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q20_31
              · have he:V = 32:=by omega
                subst V
                exact q20_32
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q20_33
              · have he:V = 34:=by omega
                subst V
                exact q20_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q20_35
              · have he:V = 36:=by omega
                subst V
                exact q20_36
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q20_37
              · have he:V = 38:=by omega
                subst V
                exact q20_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q20_39
              · have he:V = 40:=by omega
                subst V
                exact q20_40
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q20_41
              · have he:V = 42:=by omega
                subst V
                exact q20_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q20_43
              · have he:V = 44:=by omega
                subst V
                exact q20_44
      · by_cases h45_61:V < 53
        · by_cases h45_53:V < 49
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q20_45
              · have he:V = 46:=by omega
                subst V
                exact q20_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q20_47
              · have he:V = 48:=by omega
                subst V
                exact q20_48
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q20_49
              · have he:V = 50:=by omega
                subst V
                exact q20_50
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q20_51
              · have he:V = 52:=by omega
                subst V
                exact q20_52
        · by_cases h53_61:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q20_53
              · have he:V = 54:=by omega
                subst V
                exact q20_54
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q20_55
              · have he:V = 56:=by omega
                subst V
                exact q20_56
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q20_57
              · have he:V = 58:=by omega
                subst V
                exact q20_58
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q20_59
              · have he:V = 60:=by omega
                subst V
                exact q20_60
  · by_cases h61_123:V < 92
    · by_cases h61_92:V < 76
      · by_cases h61_76:V < 68
        · by_cases h61_68:V < 64
          · by_cases h61_64:V < 62
            · have he:V = 61:=by omega
              subst V
              exact q20_61
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q20_62
              · have he:V = 63:=by omega
                subst V
                exact q20_63
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q20_64
              · have he:V = 65:=by omega
                subst V
                exact q20_65
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q20_66
              · have he:V = 67:=by omega
                subst V
                exact q20_67
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q20_68
              · have he:V = 69:=by omega
                subst V
                exact q20_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q20_70
              · have he:V = 71:=by omega
                subst V
                exact q20_71
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q20_72
              · have he:V = 73:=by omega
                subst V
                exact q20_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q20_74
              · have he:V = 75:=by omega
                subst V
                exact q20_75
      · by_cases h76_92:V < 84
        · by_cases h76_84:V < 80
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q20_76
              · have he:V = 77:=by omega
                subst V
                exact q20_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q20_78
              · have he:V = 79:=by omega
                subst V
                exact q20_79
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q20_80
              · have he:V = 81:=by omega
                subst V
                exact q20_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q20_82
              · have he:V = 83:=by omega
                subst V
                exact q20_83
        · by_cases h84_92:V < 88
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q20_84
              · have he:V = 85:=by omega
                subst V
                exact q20_85
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q20_86
              · have he:V = 87:=by omega
                subst V
                exact q20_87
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q20_88
              · have he:V = 89:=by omega
                subst V
                exact q20_89
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q20_90
              · have he:V = 91:=by omega
                subst V
                exact q20_91
    · by_cases h92_123:V < 107
      · by_cases h92_107:V < 99
        · by_cases h92_99:V < 95
          · by_cases h92_95:V < 93
            · have he:V = 92:=by omega
              subst V
              exact q20_92
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q20_93
              · have he:V = 94:=by omega
                subst V
                exact q20_94
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q20_95
              · have he:V = 96:=by omega
                subst V
                exact q20_96
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q20_97
              · have he:V = 98:=by omega
                subst V
                exact q20_98
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q20_99
              · have he:V = 100:=by omega
                subst V
                exact q20_100
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q20_101
              · have he:V = 102:=by omega
                subst V
                exact q20_102
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q20_103
              · have he:V = 104:=by omega
                subst V
                exact q20_104
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q20_105
              · have he:V = 106:=by omega
                subst V
                exact q20_106
      · by_cases h107_123:V < 115
        · by_cases h107_115:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q20_107
              · have he:V = 108:=by omega
                subst V
                exact q20_108
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q20_109
              · have he:V = 110:=by omega
                subst V
                exact q20_110
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q20_111
              · have he:V = 112:=by omega
                subst V
                exact q20_112
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q20_113
              · have he:V = 114:=by omega
                subst V
                exact q20_114
        · by_cases h115_123:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q20_115
              · have he:V = 116:=by omega
                subst V
                exact q20_116
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q20_117
              · have he:V = 118:=by omega
                subst V
                exact q20_118
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q20_119
              · have he:V = 120:=by omega
                subst V
                exact q20_120
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q20_121
              · have he:V = 122:=by omega
                subst V
                exact q20_122
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
