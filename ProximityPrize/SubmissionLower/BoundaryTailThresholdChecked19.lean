import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked18

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q19_0:ThresholdAt 19 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 0 0 (by decide +kernel)
  | exact S 19 0 1 (by decide +kernel)
  | exact S 19 0 2 (by decide +kernel)
  | exact S 19 0 3 (by decide +kernel)
  | exact S 19 0 4 (by decide +kernel)
  | exact S 19 0 5 (by decide +kernel)
theorem q19_1:ThresholdAt 19 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 1 0 (by decide +kernel)
  | exact S 19 1 1 (by decide +kernel)
  | exact S 19 1 2 (by decide +kernel)
  | exact S 19 1 3 (by decide +kernel)
  | exact S 19 1 4 (by decide +kernel)
  | exact S 19 1 5 (by decide +kernel)
theorem q19_2:ThresholdAt 19 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 2 0 (by decide +kernel)
  | exact S 19 2 1 (by decide +kernel)
  | exact S 19 2 2 (by decide +kernel)
  | exact S 19 2 3 (by decide +kernel)
  | exact S 19 2 4 (by decide +kernel)
  | exact S 19 2 5 (by decide +kernel)
theorem q19_3:ThresholdAt 19 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 3 0 (by decide +kernel)
  | exact S 19 3 1 (by decide +kernel)
  | exact S 19 3 2 (by decide +kernel)
  | exact S 19 3 3 (by decide +kernel)
  | exact S 19 3 4 (by decide +kernel)
  | exact S 19 3 5 (by decide +kernel)
theorem q19_4:ThresholdAt 19 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 4 0 (by decide +kernel)
  | exact S 19 4 1 (by decide +kernel)
  | exact S 19 4 2 (by decide +kernel)
  | exact S 19 4 3 (by decide +kernel)
  | exact S 19 4 4 (by decide +kernel)
  | exact S 19 4 5 (by decide +kernel)
theorem q19_5:ThresholdAt 19 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 5 0 (by decide +kernel)
  | exact S 19 5 1 (by decide +kernel)
  | exact S 19 5 2 (by decide +kernel)
  | exact S 19 5 3 (by decide +kernel)
  | exact S 19 5 4 (by decide +kernel)
  | exact S 19 5 5 (by decide +kernel)
theorem q19_6:ThresholdAt 19 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 6 0 (by decide +kernel)
  | exact S 19 6 1 (by decide +kernel)
  | exact S 19 6 2 (by decide +kernel)
  | exact S 19 6 3 (by decide +kernel)
  | exact S 19 6 4 (by decide +kernel)
  | exact S 19 6 5 (by decide +kernel)
theorem q19_7:ThresholdAt 19 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 7 0 (by decide +kernel)
  | exact S 19 7 1 (by decide +kernel)
  | exact S 19 7 2 (by decide +kernel)
  | exact S 19 7 3 (by decide +kernel)
  | exact S 19 7 4 (by decide +kernel)
  | exact S 19 7 5 (by decide +kernel)
theorem q19_8:ThresholdAt 19 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 8 0 (by decide +kernel)
  | exact S 19 8 1 (by decide +kernel)
  | exact S 19 8 2 (by decide +kernel)
  | exact S 19 8 3 (by decide +kernel)
  | exact S 19 8 4 (by decide +kernel)
  | exact S 19 8 5 (by decide +kernel)
theorem q19_9:ThresholdAt 19 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 9 0 (by decide +kernel)
  | exact S 19 9 1 (by decide +kernel)
  | exact S 19 9 2 (by decide +kernel)
  | exact S 19 9 3 (by decide +kernel)
  | exact S 19 9 4 (by decide +kernel)
  | exact S 19 9 5 (by decide +kernel)
theorem q19_10:ThresholdAt 19 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 10 0 (by decide +kernel)
  | exact S 19 10 1 (by decide +kernel)
  | exact S 19 10 2 (by decide +kernel)
  | exact S 19 10 3 (by decide +kernel)
  | exact S 19 10 4 (by decide +kernel)
  | exact S 19 10 5 (by decide +kernel)
theorem q19_11:ThresholdAt 19 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 11 0 (by decide +kernel)
  | exact S 19 11 1 (by decide +kernel)
  | exact S 19 11 2 (by decide +kernel)
  | exact S 19 11 3 (by decide +kernel)
  | exact S 19 11 4 (by decide +kernel)
  | exact S 19 11 5 (by decide +kernel)
theorem q19_12:ThresholdAt 19 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 12 0 (by decide +kernel)
  | exact S 19 12 1 (by decide +kernel)
  | exact S 19 12 2 (by decide +kernel)
  | exact S 19 12 3 (by decide +kernel)
  | exact S 19 12 4 (by decide +kernel)
  | exact S 19 12 5 (by decide +kernel)
theorem q19_13:ThresholdAt 19 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 13 0 (by decide +kernel)
  | exact S 19 13 1 (by decide +kernel)
  | exact S 19 13 2 (by decide +kernel)
  | exact S 19 13 3 (by decide +kernel)
  | exact S 19 13 4 (by decide +kernel)
  | exact S 19 13 5 (by decide +kernel)
theorem q19_14:ThresholdAt 19 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 14 0 (by decide +kernel)
  | exact S 19 14 1 (by decide +kernel)
  | exact S 19 14 2 (by decide +kernel)
  | exact S 19 14 3 (by decide +kernel)
  | exact S 19 14 4 (by decide +kernel)
  | exact S 19 14 5 (by decide +kernel)
theorem q19_15:ThresholdAt 19 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 15 0 (by decide +kernel)
  | exact S 19 15 1 (by decide +kernel)
  | exact S 19 15 2 (by decide +kernel)
  | exact S 19 15 3 (by decide +kernel)
  | exact S 19 15 4 (by decide +kernel)
  | exact S 19 15 5 (by decide +kernel)
theorem q19_16:ThresholdAt 19 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 16 0 (by decide +kernel)
  | exact S 19 16 1 (by decide +kernel)
  | exact S 19 16 2 (by decide +kernel)
  | exact S 19 16 3 (by decide +kernel)
  | exact S 19 16 4 (by decide +kernel)
  | exact S 19 16 5 (by decide +kernel)
theorem q19_17:ThresholdAt 19 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 17 0 (by decide +kernel)
  | exact S 19 17 1 (by decide +kernel)
  | exact S 19 17 2 (by decide +kernel)
  | exact S 19 17 3 (by decide +kernel)
  | exact S 19 17 4 (by decide +kernel)
  | exact S 19 17 5 (by decide +kernel)
theorem q19_18:ThresholdAt 19 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 18 0 (by decide +kernel)
  | exact S 19 18 1 (by decide +kernel)
  | exact S 19 18 2 (by decide +kernel)
  | exact S 19 18 3 (by decide +kernel)
  | exact S 19 18 4 (by decide +kernel)
  | exact S 19 18 5 (by decide +kernel)
theorem q19_19:ThresholdAt 19 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 19 0 (by decide +kernel)
  | exact S 19 19 1 (by decide +kernel)
  | exact S 19 19 2 (by decide +kernel)
  | exact S 19 19 3 (by decide +kernel)
  | exact S 19 19 4 (by decide +kernel)
  | exact S 19 19 5 (by decide +kernel)
theorem q19_20:ThresholdAt 19 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 20 0 (by decide +kernel)
  | exact S 19 20 1 (by decide +kernel)
  | exact S 19 20 2 (by decide +kernel)
  | exact S 19 20 3 (by decide +kernel)
  | exact S 19 20 4 (by decide +kernel)
  | exact S 19 20 5 (by decide +kernel)
theorem q19_21:ThresholdAt 19 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 21 0 (by decide +kernel)
  | exact S 19 21 1 (by decide +kernel)
  | exact S 19 21 2 (by decide +kernel)
  | exact S 19 21 3 (by decide +kernel)
  | exact S 19 21 4 (by decide +kernel)
  | exact S 19 21 5 (by decide +kernel)
theorem q19_22:ThresholdAt 19 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 22 0 (by decide +kernel)
  | exact S 19 22 1 (by decide +kernel)
  | exact S 19 22 2 (by decide +kernel)
  | exact S 19 22 3 (by decide +kernel)
  | exact S 19 22 4 (by decide +kernel)
  | exact S 19 22 5 (by decide +kernel)
theorem q19_23:ThresholdAt 19 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 23 0 (by decide +kernel)
  | exact S 19 23 1 (by decide +kernel)
  | exact S 19 23 2 (by decide +kernel)
  | exact S 19 23 3 (by decide +kernel)
  | exact S 19 23 4 (by decide +kernel)
  | exact S 19 23 5 (by decide +kernel)
theorem q19_24:ThresholdAt 19 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 24 0 (by decide +kernel)
  | exact S 19 24 1 (by decide +kernel)
  | exact S 19 24 2 (by decide +kernel)
  | exact S 19 24 3 (by decide +kernel)
  | exact S 19 24 4 (by decide +kernel)
  | exact S 19 24 5 (by decide +kernel)
theorem q19_25:ThresholdAt 19 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 25 0 (by decide +kernel)
  | exact S 19 25 1 (by decide +kernel)
  | exact S 19 25 2 (by decide +kernel)
  | exact S 19 25 3 (by decide +kernel)
  | exact S 19 25 4 (by decide +kernel)
  | exact S 19 25 5 (by decide +kernel)
theorem q19_26:ThresholdAt 19 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 26 0 (by decide +kernel)
  | exact S 19 26 1 (by decide +kernel)
  | exact S 19 26 2 (by decide +kernel)
  | exact S 19 26 3 (by decide +kernel)
  | exact S 19 26 4 (by decide +kernel)
  | exact S 19 26 5 (by decide +kernel)
theorem q19_27:ThresholdAt 19 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 27 0 (by decide +kernel)
  | exact S 19 27 1 (by decide +kernel)
  | exact S 19 27 2 (by decide +kernel)
  | exact S 19 27 3 (by decide +kernel)
  | exact S 19 27 4 (by decide +kernel)
  | exact S 19 27 5 (by decide +kernel)
theorem q19_28:ThresholdAt 19 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 28 0 (by decide +kernel)
  | exact S 19 28 1 (by decide +kernel)
  | exact S 19 28 2 (by decide +kernel)
  | exact S 19 28 3 (by decide +kernel)
  | exact S 19 28 4 (by decide +kernel)
  | exact S 19 28 5 (by decide +kernel)
theorem q19_29:ThresholdAt 19 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 29 0 (by decide +kernel)
  | exact S 19 29 1 (by decide +kernel)
  | exact S 19 29 2 (by decide +kernel)
  | exact S 19 29 3 (by decide +kernel)
  | exact S 19 29 4 (by decide +kernel)
  | exact S 19 29 5 (by decide +kernel)
theorem q19_30:ThresholdAt 19 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 30 0 (by decide +kernel)
  | exact S 19 30 1 (by decide +kernel)
  | exact S 19 30 2 (by decide +kernel)
  | exact S 19 30 3 (by decide +kernel)
  | exact S 19 30 4 (by decide +kernel)
  | exact S 19 30 5 (by decide +kernel)
theorem q19_31:ThresholdAt 19 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 31 0 (by decide +kernel)
  | exact S 19 31 1 (by decide +kernel)
  | exact S 19 31 2 (by decide +kernel)
  | exact S 19 31 3 (by decide +kernel)
  | exact S 19 31 4 (by decide +kernel)
  | exact S 19 31 5 (by decide +kernel)
theorem q19_32:ThresholdAt 19 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 32 0 (by decide +kernel)
  | exact S 19 32 1 (by decide +kernel)
  | exact S 19 32 2 (by decide +kernel)
  | exact S 19 32 3 (by decide +kernel)
  | exact S 19 32 4 (by decide +kernel)
  | exact S 19 32 5 (by decide +kernel)
theorem q19_33:ThresholdAt 19 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 33 0 (by decide +kernel)
  | exact S 19 33 1 (by decide +kernel)
  | exact S 19 33 2 (by decide +kernel)
  | exact S 19 33 3 (by decide +kernel)
  | exact S 19 33 4 (by decide +kernel)
  | exact S 19 33 5 (by decide +kernel)
theorem q19_34:ThresholdAt 19 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 34 0 (by decide +kernel)
  | exact S 19 34 1 (by decide +kernel)
  | exact S 19 34 2 (by decide +kernel)
  | exact S 19 34 3 (by decide +kernel)
  | exact S 19 34 4 (by decide +kernel)
  | exact S 19 34 5 (by decide +kernel)
theorem q19_35:ThresholdAt 19 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 35 0 (by decide +kernel)
  | exact S 19 35 1 (by decide +kernel)
  | exact S 19 35 2 (by decide +kernel)
  | exact S 19 35 3 (by decide +kernel)
  | exact S 19 35 4 (by decide +kernel)
  | exact S 19 35 5 (by decide +kernel)
theorem q19_36:ThresholdAt 19 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 36 0 (by decide +kernel)
  | exact S 19 36 1 (by decide +kernel)
  | exact S 19 36 2 (by decide +kernel)
  | exact S 19 36 3 (by decide +kernel)
  | exact S 19 36 4 (by decide +kernel)
  | exact S 19 36 5 (by decide +kernel)
theorem q19_37:ThresholdAt 19 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 37 0 (by decide +kernel)
  | exact S 19 37 1 (by decide +kernel)
  | exact S 19 37 2 (by decide +kernel)
  | exact S 19 37 3 (by decide +kernel)
  | exact S 19 37 4 (by decide +kernel)
  | exact S 19 37 5 (by decide +kernel)
theorem q19_38:ThresholdAt 19 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 38 0 (by decide +kernel)
  | exact S 19 38 1 (by decide +kernel)
  | exact S 19 38 2 (by decide +kernel)
  | exact S 19 38 3 (by decide +kernel)
  | exact S 19 38 4 (by decide +kernel)
  | exact S 19 38 5 (by decide +kernel)
theorem q19_39:ThresholdAt 19 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 39 0 (by decide +kernel)
  | exact S 19 39 1 (by decide +kernel)
  | exact S 19 39 2 (by decide +kernel)
  | exact S 19 39 3 (by decide +kernel)
  | exact S 19 39 4 (by decide +kernel)
  | exact S 19 39 5 (by decide +kernel)
theorem q19_40:ThresholdAt 19 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 40 0 (by decide +kernel)
  | exact S 19 40 1 (by decide +kernel)
  | exact S 19 40 2 (by decide +kernel)
  | exact S 19 40 3 (by decide +kernel)
  | exact S 19 40 4 (by decide +kernel)
  | exact S 19 40 5 (by decide +kernel)
theorem q19_41:ThresholdAt 19 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 41 0 (by decide +kernel)
  | exact S 19 41 1 (by decide +kernel)
  | exact S 19 41 2 (by decide +kernel)
  | exact S 19 41 3 (by decide +kernel)
  | exact S 19 41 4 (by decide +kernel)
  | exact S 19 41 5 (by decide +kernel)
theorem q19_42:ThresholdAt 19 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 42 0 (by decide +kernel)
  | exact S 19 42 1 (by decide +kernel)
  | exact S 19 42 2 (by decide +kernel)
  | exact S 19 42 3 (by decide +kernel)
  | exact S 19 42 4 (by decide +kernel)
  | exact S 19 42 5 (by decide +kernel)
theorem q19_43:ThresholdAt 19 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 43 0 (by decide +kernel)
  | exact S 19 43 1 (by decide +kernel)
  | exact S 19 43 2 (by decide +kernel)
  | exact S 19 43 3 (by decide +kernel)
  | exact S 19 43 4 (by decide +kernel)
  | exact S 19 43 5 (by decide +kernel)
theorem q19_44:ThresholdAt 19 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 44 0 (by decide +kernel)
  | exact S 19 44 1 (by decide +kernel)
  | exact S 19 44 2 (by decide +kernel)
  | exact S 19 44 3 (by decide +kernel)
  | exact S 19 44 4 (by decide +kernel)
  | exact S 19 44 5 (by decide +kernel)
theorem q19_45:ThresholdAt 19 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 45 0 (by decide +kernel)
  | exact S 19 45 1 (by decide +kernel)
  | exact S 19 45 2 (by decide +kernel)
  | exact S 19 45 3 (by decide +kernel)
  | exact S 19 45 4 (by decide +kernel)
  | exact S 19 45 5 (by decide +kernel)
theorem q19_46:ThresholdAt 19 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 46 0 (by decide +kernel)
  | exact S 19 46 1 (by decide +kernel)
  | exact S 19 46 2 (by decide +kernel)
  | exact S 19 46 3 (by decide +kernel)
  | exact S 19 46 4 (by decide +kernel)
  | exact S 19 46 5 (by decide +kernel)
theorem q19_47:ThresholdAt 19 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 47 0 (by decide +kernel)
  | exact S 19 47 1 (by decide +kernel)
  | exact S 19 47 2 (by decide +kernel)
  | exact S 19 47 3 (by decide +kernel)
  | exact S 19 47 4 (by decide +kernel)
  | exact S 19 47 5 (by decide +kernel)
theorem q19_48:ThresholdAt 19 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 48 0 (by decide +kernel)
  | exact S 19 48 1 (by decide +kernel)
  | exact S 19 48 2 (by decide +kernel)
  | exact S 19 48 3 (by decide +kernel)
  | exact S 19 48 4 (by decide +kernel)
  | exact S 19 48 5 (by decide +kernel)
theorem q19_49:ThresholdAt 19 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 49 0 (by decide +kernel)
  | exact S 19 49 1 (by decide +kernel)
  | exact S 19 49 2 (by decide +kernel)
  | exact S 19 49 3 (by decide +kernel)
  | exact S 19 49 4 (by decide +kernel)
  | exact S 19 49 5 (by decide +kernel)
theorem q19_50:ThresholdAt 19 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 50 0 (by decide +kernel)
  | exact S 19 50 1 (by decide +kernel)
  | exact S 19 50 2 (by decide +kernel)
  | exact S 19 50 3 (by decide +kernel)
  | exact S 19 50 4 (by decide +kernel)
  | exact S 19 50 5 (by decide +kernel)
theorem q19_51:ThresholdAt 19 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 51 0 (by decide +kernel)
  | exact S 19 51 1 (by decide +kernel)
  | exact S 19 51 2 (by decide +kernel)
  | exact S 19 51 3 (by decide +kernel)
  | exact S 19 51 4 (by decide +kernel)
  | exact S 19 51 5 (by decide +kernel)
theorem q19_52:ThresholdAt 19 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 52 0 (by decide +kernel)
  | exact S 19 52 1 (by decide +kernel)
  | exact S 19 52 2 (by decide +kernel)
  | exact S 19 52 3 (by decide +kernel)
  | exact S 19 52 4 (by decide +kernel)
  | exact S 19 52 5 (by decide +kernel)
theorem q19_53:ThresholdAt 19 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 53 0 (by decide +kernel)
  | exact S 19 53 1 (by decide +kernel)
  | exact S 19 53 2 (by decide +kernel)
  | exact S 19 53 3 (by decide +kernel)
  | exact S 19 53 4 (by decide +kernel)
  | exact S 19 53 5 (by decide +kernel)
theorem q19_54:ThresholdAt 19 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 54 0 (by decide +kernel)
  | exact S 19 54 1 (by decide +kernel)
  | exact S 19 54 2 (by decide +kernel)
  | exact S 19 54 3 (by decide +kernel)
  | exact S 19 54 4 (by decide +kernel)
  | exact S 19 54 5 (by decide +kernel)
theorem q19_55:ThresholdAt 19 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 55 0 (by decide +kernel)
  | exact S 19 55 1 (by decide +kernel)
  | exact S 19 55 2 (by decide +kernel)
  | exact S 19 55 3 (by decide +kernel)
  | exact S 19 55 4 (by decide +kernel)
  | exact S 19 55 5 (by decide +kernel)
theorem q19_56:ThresholdAt 19 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 56 0 (by decide +kernel)
  | exact S 19 56 1 (by decide +kernel)
  | exact S 19 56 2 (by decide +kernel)
  | exact S 19 56 3 (by decide +kernel)
  | exact S 19 56 4 (by decide +kernel)
  | exact S 19 56 5 (by decide +kernel)
theorem q19_57:ThresholdAt 19 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 57 0 (by decide +kernel)
  | exact S 19 57 1 (by decide +kernel)
  | exact S 19 57 2 (by decide +kernel)
  | exact S 19 57 3 (by decide +kernel)
  | exact S 19 57 4 (by decide +kernel)
  | exact S 19 57 5 (by decide +kernel)
theorem q19_58:ThresholdAt 19 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 58 0 (by decide +kernel)
  | exact S 19 58 1 (by decide +kernel)
  | exact S 19 58 2 (by decide +kernel)
  | exact S 19 58 3 (by decide +kernel)
  | exact S 19 58 4 (by decide +kernel)
  | exact S 19 58 5 (by decide +kernel)
theorem q19_59:ThresholdAt 19 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 59 0 (by decide +kernel)
  | exact S 19 59 1 (by decide +kernel)
  | exact S 19 59 2 (by decide +kernel)
  | exact S 19 59 3 (by decide +kernel)
  | exact S 19 59 4 (by decide +kernel)
  | exact S 19 59 5 (by decide +kernel)
theorem q19_60:ThresholdAt 19 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 60 0 (by decide +kernel)
  | exact S 19 60 1 (by decide +kernel)
  | exact S 19 60 2 (by decide +kernel)
  | exact S 19 60 3 (by decide +kernel)
  | exact S 19 60 4 (by decide +kernel)
  | exact S 19 60 5 (by decide +kernel)
theorem q19_61:ThresholdAt 19 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 61 0 (by decide +kernel)
  | exact S 19 61 1 (by decide +kernel)
  | exact S 19 61 2 (by decide +kernel)
  | exact S 19 61 3 (by decide +kernel)
  | exact S 19 61 4 (by decide +kernel)
  | exact S 19 61 5 (by decide +kernel)
theorem q19_62:ThresholdAt 19 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 62 0 (by decide +kernel)
  | exact S 19 62 1 (by decide +kernel)
  | exact S 19 62 2 (by decide +kernel)
  | exact S 19 62 3 (by decide +kernel)
  | exact S 19 62 4 (by decide +kernel)
  | exact S 19 62 5 (by decide +kernel)
theorem q19_63:ThresholdAt 19 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 63 0 (by decide +kernel)
  | exact S 19 63 1 (by decide +kernel)
  | exact S 19 63 2 (by decide +kernel)
  | exact S 19 63 3 (by decide +kernel)
  | exact S 19 63 4 (by decide +kernel)
  | exact S 19 63 5 (by decide +kernel)
theorem q19_64:ThresholdAt 19 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 64 0 (by decide +kernel)
  | exact S 19 64 1 (by decide +kernel)
  | exact S 19 64 2 (by decide +kernel)
  | exact S 19 64 3 (by decide +kernel)
  | exact S 19 64 4 (by decide +kernel)
  | exact S 19 64 5 (by decide +kernel)
theorem q19_65:ThresholdAt 19 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 65 0 (by decide +kernel)
  | exact S 19 65 1 (by decide +kernel)
  | exact S 19 65 2 (by decide +kernel)
  | exact S 19 65 3 (by decide +kernel)
  | exact S 19 65 4 (by decide +kernel)
  | exact S 19 65 5 (by decide +kernel)
theorem q19_66:ThresholdAt 19 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 66 0 (by decide +kernel)
  | exact S 19 66 1 (by decide +kernel)
  | exact S 19 66 2 (by decide +kernel)
  | exact S 19 66 3 (by decide +kernel)
  | exact S 19 66 4 (by decide +kernel)
  | exact S 19 66 5 (by decide +kernel)
theorem q19_67:ThresholdAt 19 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 67 0 (by decide +kernel)
  | exact S 19 67 1 (by decide +kernel)
  | exact S 19 67 2 (by decide +kernel)
  | exact S 19 67 3 (by decide +kernel)
  | exact S 19 67 4 (by decide +kernel)
  | exact S 19 67 5 (by decide +kernel)
theorem q19_68:ThresholdAt 19 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 68 0 (by decide +kernel)
  | exact S 19 68 1 (by decide +kernel)
  | exact S 19 68 2 (by decide +kernel)
  | exact S 19 68 3 (by decide +kernel)
  | exact S 19 68 4 (by decide +kernel)
  | exact S 19 68 5 (by decide +kernel)
theorem q19_69:ThresholdAt 19 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 69 0 (by decide +kernel)
  | exact S 19 69 1 (by decide +kernel)
  | exact S 19 69 2 (by decide +kernel)
  | exact S 19 69 3 (by decide +kernel)
  | exact S 19 69 4 (by decide +kernel)
  | exact S 19 69 5 (by decide +kernel)
theorem q19_70:ThresholdAt 19 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 70 0 (by decide +kernel)
  | exact S 19 70 1 (by decide +kernel)
  | exact S 19 70 2 (by decide +kernel)
  | exact S 19 70 3 (by decide +kernel)
  | exact S 19 70 4 (by decide +kernel)
  | exact S 19 70 5 (by decide +kernel)
theorem q19_71:ThresholdAt 19 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 71 0 (by decide +kernel)
  | exact S 19 71 1 (by decide +kernel)
  | exact S 19 71 2 (by decide +kernel)
  | exact S 19 71 3 (by decide +kernel)
  | exact S 19 71 4 (by decide +kernel)
  | exact S 19 71 5 (by decide +kernel)
theorem q19_72:ThresholdAt 19 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 72 0 (by decide +kernel)
  | exact S 19 72 1 (by decide +kernel)
  | exact S 19 72 2 (by decide +kernel)
  | exact S 19 72 3 (by decide +kernel)
  | exact S 19 72 4 (by decide +kernel)
  | exact S 19 72 5 (by decide +kernel)
theorem q19_73:ThresholdAt 19 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 73 0 (by decide +kernel)
  | exact S 19 73 1 (by decide +kernel)
  | exact S 19 73 2 (by decide +kernel)
  | exact S 19 73 3 (by decide +kernel)
  | exact S 19 73 4 (by decide +kernel)
  | exact S 19 73 5 (by decide +kernel)
theorem q19_74:ThresholdAt 19 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 74 0 (by decide +kernel)
  | exact S 19 74 1 (by decide +kernel)
  | exact S 19 74 2 (by decide +kernel)
  | exact S 19 74 3 (by decide +kernel)
  | exact S 19 74 4 (by decide +kernel)
  | exact S 19 74 5 (by decide +kernel)
theorem q19_75:ThresholdAt 19 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 75 0 (by decide +kernel)
  | exact S 19 75 1 (by decide +kernel)
  | exact S 19 75 2 (by decide +kernel)
  | exact S 19 75 3 (by decide +kernel)
  | exact S 19 75 4 (by decide +kernel)
  | exact S 19 75 5 (by decide +kernel)
theorem q19_76:ThresholdAt 19 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 76 0 (by decide +kernel)
  | exact S 19 76 1 (by decide +kernel)
  | exact S 19 76 2 (by decide +kernel)
  | exact S 19 76 3 (by decide +kernel)
  | exact S 19 76 4 (by decide +kernel)
  | exact S 19 76 5 (by decide +kernel)
theorem q19_77:ThresholdAt 19 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 77 0 (by decide +kernel)
  | exact S 19 77 1 (by decide +kernel)
  | exact S 19 77 2 (by decide +kernel)
  | exact S 19 77 3 (by decide +kernel)
  | exact S 19 77 4 (by decide +kernel)
  | exact S 19 77 5 (by decide +kernel)
theorem q19_78:ThresholdAt 19 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 78 0 (by decide +kernel)
  | exact S 19 78 1 (by decide +kernel)
  | exact S 19 78 2 (by decide +kernel)
  | exact S 19 78 3 (by decide +kernel)
  | exact S 19 78 4 (by decide +kernel)
  | exact S 19 78 5 (by decide +kernel)
theorem q19_79:ThresholdAt 19 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 79 0 (by decide +kernel)
  | exact S 19 79 1 (by decide +kernel)
  | exact S 19 79 2 (by decide +kernel)
  | exact S 19 79 3 (by decide +kernel)
  | exact S 19 79 4 (by decide +kernel)
  | exact S 19 79 5 (by decide +kernel)
theorem q19_80:ThresholdAt 19 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 80 0 (by decide +kernel)
  | exact S 19 80 1 (by decide +kernel)
  | exact S 19 80 2 (by decide +kernel)
  | exact S 19 80 3 (by decide +kernel)
  | exact S 19 80 4 (by decide +kernel)
  | exact S 19 80 5 (by decide +kernel)
theorem q19_81:ThresholdAt 19 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 81 0 (by decide +kernel)
  | exact S 19 81 1 (by decide +kernel)
  | exact S 19 81 2 (by decide +kernel)
  | exact S 19 81 3 (by decide +kernel)
  | exact S 19 81 4 (by decide +kernel)
  | exact S 19 81 5 (by decide +kernel)
theorem q19_82:ThresholdAt 19 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 82 0 (by decide +kernel)
  | exact S 19 82 1 (by decide +kernel)
  | exact S 19 82 2 (by decide +kernel)
  | exact S 19 82 3 (by decide +kernel)
  | exact S 19 82 4 (by decide +kernel)
  | exact S 19 82 5 (by decide +kernel)
theorem q19_83:ThresholdAt 19 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 83 0 (by decide +kernel)
  | exact S 19 83 1 (by decide +kernel)
  | exact S 19 83 2 (by decide +kernel)
  | exact S 19 83 3 (by decide +kernel)
  | exact S 19 83 4 (by decide +kernel)
  | exact S 19 83 5 (by decide +kernel)
theorem q19_84:ThresholdAt 19 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 84 0 (by decide +kernel)
  | exact S 19 84 1 (by decide +kernel)
  | exact S 19 84 2 (by decide +kernel)
  | exact S 19 84 3 (by decide +kernel)
  | exact S 19 84 4 (by decide +kernel)
  | exact S 19 84 5 (by decide +kernel)
theorem q19_85:ThresholdAt 19 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 85 0 (by decide +kernel)
  | exact S 19 85 1 (by decide +kernel)
  | exact S 19 85 2 (by decide +kernel)
  | exact S 19 85 3 (by decide +kernel)
  | exact S 19 85 4 (by decide +kernel)
  | exact S 19 85 5 (by decide +kernel)
theorem q19_86:ThresholdAt 19 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 86 0 (by decide +kernel)
  | exact S 19 86 1 (by decide +kernel)
  | exact S 19 86 2 (by decide +kernel)
  | exact S 19 86 3 (by decide +kernel)
  | exact S 19 86 4 (by decide +kernel)
  | exact S 19 86 5 (by decide +kernel)
theorem q19_87:ThresholdAt 19 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 87 0 (by decide +kernel)
  | exact S 19 87 1 (by decide +kernel)
  | exact S 19 87 2 (by decide +kernel)
  | exact S 19 87 3 (by decide +kernel)
  | exact S 19 87 4 (by decide +kernel)
  | exact S 19 87 5 (by decide +kernel)
theorem q19_88:ThresholdAt 19 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 88 0 (by decide +kernel)
  | exact S 19 88 1 (by decide +kernel)
  | exact S 19 88 2 (by decide +kernel)
  | exact S 19 88 3 (by decide +kernel)
  | exact S 19 88 4 (by decide +kernel)
  | exact S 19 88 5 (by decide +kernel)
theorem q19_89:ThresholdAt 19 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 89 0 (by decide +kernel)
  | exact S 19 89 1 (by decide +kernel)
  | exact S 19 89 2 (by decide +kernel)
  | exact S 19 89 3 (by decide +kernel)
  | exact S 19 89 4 (by decide +kernel)
  | exact S 19 89 5 (by decide +kernel)
theorem q19_90:ThresholdAt 19 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 90 0 (by decide +kernel)
  | exact S 19 90 1 (by decide +kernel)
  | exact S 19 90 2 (by decide +kernel)
  | exact S 19 90 3 (by decide +kernel)
  | exact S 19 90 4 (by decide +kernel)
  | exact S 19 90 5 (by decide +kernel)
theorem q19_91:ThresholdAt 19 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 91 0 (by decide +kernel)
  | exact S 19 91 1 (by decide +kernel)
  | exact S 19 91 2 (by decide +kernel)
  | exact S 19 91 3 (by decide +kernel)
  | exact S 19 91 4 (by decide +kernel)
  | exact S 19 91 5 (by decide +kernel)
theorem q19_92:ThresholdAt 19 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 92 0 (by decide +kernel)
  | exact S 19 92 1 (by decide +kernel)
  | exact S 19 92 2 (by decide +kernel)
  | exact S 19 92 3 (by decide +kernel)
  | exact S 19 92 4 (by decide +kernel)
  | exact S 19 92 5 (by decide +kernel)
theorem q19_93:ThresholdAt 19 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 93 0 (by decide +kernel)
  | exact S 19 93 1 (by decide +kernel)
  | exact S 19 93 2 (by decide +kernel)
  | exact S 19 93 3 (by decide +kernel)
  | exact S 19 93 4 (by decide +kernel)
  | exact S 19 93 5 (by decide +kernel)
theorem q19_94:ThresholdAt 19 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 94 0 (by decide +kernel)
  | exact S 19 94 1 (by decide +kernel)
  | exact S 19 94 2 (by decide +kernel)
  | exact S 19 94 3 (by decide +kernel)
  | exact S 19 94 4 (by decide +kernel)
  | exact S 19 94 5 (by decide +kernel)
theorem q19_95:ThresholdAt 19 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 95 0 (by decide +kernel)
  | exact S 19 95 1 (by decide +kernel)
  | exact S 19 95 2 (by decide +kernel)
  | exact S 19 95 3 (by decide +kernel)
  | exact S 19 95 4 (by decide +kernel)
  | exact S 19 95 5 (by decide +kernel)
theorem q19_96:ThresholdAt 19 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 96 0 (by decide +kernel)
  | exact S 19 96 1 (by decide +kernel)
  | exact S 19 96 2 (by decide +kernel)
  | exact S 19 96 3 (by decide +kernel)
  | exact S 19 96 4 (by decide +kernel)
  | exact S 19 96 5 (by decide +kernel)
theorem q19_97:ThresholdAt 19 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 97 0 (by decide +kernel)
  | exact S 19 97 1 (by decide +kernel)
  | exact S 19 97 2 (by decide +kernel)
  | exact S 19 97 3 (by decide +kernel)
  | exact S 19 97 4 (by decide +kernel)
  | exact S 19 97 5 (by decide +kernel)
theorem q19_98:ThresholdAt 19 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 98 0 (by decide +kernel)
  | exact S 19 98 1 (by decide +kernel)
  | exact S 19 98 2 (by decide +kernel)
  | exact S 19 98 3 (by decide +kernel)
  | exact S 19 98 4 (by decide +kernel)
  | exact S 19 98 5 (by decide +kernel)
theorem q19_99:ThresholdAt 19 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 99 0 (by decide +kernel)
  | exact S 19 99 1 (by decide +kernel)
  | exact S 19 99 2 (by decide +kernel)
  | exact S 19 99 3 (by decide +kernel)
  | exact S 19 99 4 (by decide +kernel)
  | exact S 19 99 5 (by decide +kernel)
theorem q19_100:ThresholdAt 19 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 100 0 (by decide +kernel)
  | exact S 19 100 1 (by decide +kernel)
  | exact S 19 100 2 (by decide +kernel)
  | exact S 19 100 3 (by decide +kernel)
  | exact S 19 100 4 (by decide +kernel)
  | exact S 19 100 5 (by decide +kernel)
theorem q19_101:ThresholdAt 19 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 101 0 (by decide +kernel)
  | exact S 19 101 1 (by decide +kernel)
  | exact S 19 101 2 (by decide +kernel)
  | exact S 19 101 3 (by decide +kernel)
  | exact S 19 101 4 (by decide +kernel)
  | exact S 19 101 5 (by decide +kernel)
theorem q19_102:ThresholdAt 19 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 102 0 (by decide +kernel)
  | exact S 19 102 1 (by decide +kernel)
  | exact S 19 102 2 (by decide +kernel)
  | exact S 19 102 3 (by decide +kernel)
  | exact S 19 102 4 (by decide +kernel)
  | exact S 19 102 5 (by decide +kernel)
theorem q19_103:ThresholdAt 19 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 103 0 (by decide +kernel)
  | exact S 19 103 1 (by decide +kernel)
  | exact S 19 103 2 (by decide +kernel)
  | exact S 19 103 3 (by decide +kernel)
  | exact S 19 103 4 (by decide +kernel)
  | exact S 19 103 5 (by decide +kernel)
theorem q19_104:ThresholdAt 19 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 104 0 (by decide +kernel)
  | exact S 19 104 1 (by decide +kernel)
  | exact S 19 104 2 (by decide +kernel)
  | exact S 19 104 3 (by decide +kernel)
  | exact S 19 104 4 (by decide +kernel)
  | exact S 19 104 5 (by decide +kernel)
theorem q19_105:ThresholdAt 19 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 105 0 (by decide +kernel)
  | exact S 19 105 1 (by decide +kernel)
  | exact S 19 105 2 (by decide +kernel)
  | exact S 19 105 3 (by decide +kernel)
  | exact S 19 105 4 (by decide +kernel)
  | exact S 19 105 5 (by decide +kernel)
theorem q19_106:ThresholdAt 19 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 106 0 (by decide +kernel)
  | exact S 19 106 1 (by decide +kernel)
  | exact S 19 106 2 (by decide +kernel)
  | exact S 19 106 3 (by decide +kernel)
  | exact S 19 106 4 (by decide +kernel)
  | exact S 19 106 5 (by decide +kernel)
theorem q19_107:ThresholdAt 19 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 107 0 (by decide +kernel)
  | exact S 19 107 1 (by decide +kernel)
  | exact S 19 107 2 (by decide +kernel)
  | exact S 19 107 3 (by decide +kernel)
  | exact S 19 107 4 (by decide +kernel)
  | exact S 19 107 5 (by decide +kernel)
theorem q19_108:ThresholdAt 19 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 108 0 (by decide +kernel)
  | exact S 19 108 1 (by decide +kernel)
  | exact S 19 108 2 (by decide +kernel)
  | exact S 19 108 3 (by decide +kernel)
  | exact S 19 108 4 (by decide +kernel)
  | exact S 19 108 5 (by decide +kernel)
theorem q19_109:ThresholdAt 19 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 109 0 (by decide +kernel)
  | exact S 19 109 1 (by decide +kernel)
  | exact S 19 109 2 (by decide +kernel)
  | exact S 19 109 3 (by decide +kernel)
  | exact S 19 109 4 (by decide +kernel)
  | exact S 19 109 5 (by decide +kernel)
theorem q19_110:ThresholdAt 19 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 110 0 (by decide +kernel)
  | exact S 19 110 1 (by decide +kernel)
  | exact S 19 110 2 (by decide +kernel)
  | exact S 19 110 3 (by decide +kernel)
  | exact S 19 110 4 (by decide +kernel)
  | exact S 19 110 5 (by decide +kernel)
theorem q19_111:ThresholdAt 19 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 111 0 (by decide +kernel)
  | exact S 19 111 1 (by decide +kernel)
  | exact S 19 111 2 (by decide +kernel)
  | exact S 19 111 3 (by decide +kernel)
  | exact S 19 111 4 (by decide +kernel)
  | exact S 19 111 5 (by decide +kernel)
theorem q19_112:ThresholdAt 19 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 112 0 (by decide +kernel)
  | exact S 19 112 1 (by decide +kernel)
  | exact S 19 112 2 (by decide +kernel)
  | exact S 19 112 3 (by decide +kernel)
  | exact S 19 112 4 (by decide +kernel)
  | exact S 19 112 5 (by decide +kernel)
theorem q19_113:ThresholdAt 19 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 113 0 (by decide +kernel)
  | exact S 19 113 1 (by decide +kernel)
  | exact S 19 113 2 (by decide +kernel)
  | exact S 19 113 3 (by decide +kernel)
  | exact S 19 113 4 (by decide +kernel)
  | exact S 19 113 5 (by decide +kernel)
theorem q19_114:ThresholdAt 19 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 114 0 (by decide +kernel)
  | exact S 19 114 1 (by decide +kernel)
  | exact S 19 114 2 (by decide +kernel)
  | exact S 19 114 3 (by decide +kernel)
  | exact S 19 114 4 (by decide +kernel)
  | exact S 19 114 5 (by decide +kernel)
theorem q19_115:ThresholdAt 19 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 115 0 (by decide +kernel)
  | exact S 19 115 1 (by decide +kernel)
  | exact S 19 115 2 (by decide +kernel)
  | exact S 19 115 3 (by decide +kernel)
  | exact S 19 115 4 (by decide +kernel)
  | exact S 19 115 5 (by decide +kernel)
theorem q19_116:ThresholdAt 19 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 116 0 (by decide +kernel)
  | exact S 19 116 1 (by decide +kernel)
  | exact S 19 116 2 (by decide +kernel)
  | exact S 19 116 3 (by decide +kernel)
  | exact S 19 116 4 (by decide +kernel)
  | exact S 19 116 5 (by decide +kernel)
theorem q19_117:ThresholdAt 19 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 117 0 (by decide +kernel)
  | exact S 19 117 1 (by decide +kernel)
  | exact S 19 117 2 (by decide +kernel)
  | exact S 19 117 3 (by decide +kernel)
  | exact S 19 117 4 (by decide +kernel)
  | exact S 19 117 5 (by decide +kernel)
theorem q19_118:ThresholdAt 19 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 118 0 (by decide +kernel)
  | exact S 19 118 1 (by decide +kernel)
  | exact S 19 118 2 (by decide +kernel)
  | exact S 19 118 3 (by decide +kernel)
  | exact S 19 118 4 (by decide +kernel)
  | exact S 19 118 5 (by decide +kernel)
theorem q19_119:ThresholdAt 19 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 119 0 (by decide +kernel)
  | exact S 19 119 1 (by decide +kernel)
  | exact S 19 119 2 (by decide +kernel)
  | exact S 19 119 3 (by decide +kernel)
  | exact S 19 119 4 (by decide +kernel)
  | exact S 19 119 5 (by decide +kernel)
theorem q19_120:ThresholdAt 19 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 120 0 (by decide +kernel)
  | exact S 19 120 1 (by decide +kernel)
  | exact S 19 120 2 (by decide +kernel)
  | exact S 19 120 3 (by decide +kernel)
  | exact S 19 120 4 (by decide +kernel)
  | exact S 19 120 5 (by decide +kernel)
theorem q19_121:ThresholdAt 19 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 121 0 (by decide +kernel)
  | exact S 19 121 1 (by decide +kernel)
  | exact S 19 121 2 (by decide +kernel)
  | exact S 19 121 3 (by decide +kernel)
  | exact S 19 121 4 (by decide +kernel)
  | exact S 19 121 5 (by decide +kernel)
theorem q19_122:ThresholdAt 19 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 122 0 (by decide +kernel)
  | exact S 19 122 1 (by decide +kernel)
  | exact S 19 122 2 (by decide +kernel)
  | exact S 19 122 3 (by decide +kernel)
  | exact S 19 122 4 (by decide +kernel)
  | exact S 19 122 5 (by decide +kernel)
theorem q19_123:ThresholdAt 19 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 123 0 (by decide +kernel)
  | exact S 19 123 1 (by decide +kernel)
  | exact S 19 123 2 (by decide +kernel)
  | exact S 19 123 3 (by decide +kernel)
  | exact S 19 123 4 (by decide +kernel)
  | exact S 19 123 5 (by decide +kernel)
theorem checkedR19:∀ V ∈ List.range 124,ThresholdAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0_124:V < 62
  · by_cases h0_62:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q19_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q19_1
              · have he:V = 2:=by omega
                subst V
                exact q19_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q19_3
              · have he:V = 4:=by omega
                subst V
                exact q19_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q19_5
              · have he:V = 6:=by omega
                subst V
                exact q19_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q19_7
              · have he:V = 8:=by omega
                subst V
                exact q19_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q19_9
              · have he:V = 10:=by omega
                subst V
                exact q19_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q19_11
              · have he:V = 12:=by omega
                subst V
                exact q19_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q19_13
              · have he:V = 14:=by omega
                subst V
                exact q19_14
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q19_15
              · have he:V = 16:=by omega
                subst V
                exact q19_16
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q19_17
              · have he:V = 18:=by omega
                subst V
                exact q19_18
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q19_19
              · have he:V = 20:=by omega
                subst V
                exact q19_20
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q19_21
              · have he:V = 22:=by omega
                subst V
                exact q19_22
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q19_23
              · have he:V = 24:=by omega
                subst V
                exact q19_24
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q19_25
              · have he:V = 26:=by omega
                subst V
                exact q19_26
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q19_27
              · have he:V = 28:=by omega
                subst V
                exact q19_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q19_29
              · have he:V = 30:=by omega
                subst V
                exact q19_30
    · by_cases h31_62:V < 46
      · by_cases h31_46:V < 38
        · by_cases h31_38:V < 34
          · by_cases h31_34:V < 32
            · have he:V = 31:=by omega
              subst V
              exact q19_31
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q19_32
              · have he:V = 33:=by omega
                subst V
                exact q19_33
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q19_34
              · have he:V = 35:=by omega
                subst V
                exact q19_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q19_36
              · have he:V = 37:=by omega
                subst V
                exact q19_37
        · by_cases h38_46:V < 42
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q19_38
              · have he:V = 39:=by omega
                subst V
                exact q19_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q19_40
              · have he:V = 41:=by omega
                subst V
                exact q19_41
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q19_42
              · have he:V = 43:=by omega
                subst V
                exact q19_43
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q19_44
              · have he:V = 45:=by omega
                subst V
                exact q19_45
      · by_cases h46_62:V < 54
        · by_cases h46_54:V < 50
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q19_46
              · have he:V = 47:=by omega
                subst V
                exact q19_47
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q19_48
              · have he:V = 49:=by omega
                subst V
                exact q19_49
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q19_50
              · have he:V = 51:=by omega
                subst V
                exact q19_51
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q19_52
              · have he:V = 53:=by omega
                subst V
                exact q19_53
        · by_cases h54_62:V < 58
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q19_54
              · have he:V = 55:=by omega
                subst V
                exact q19_55
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q19_56
              · have he:V = 57:=by omega
                subst V
                exact q19_57
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q19_58
              · have he:V = 59:=by omega
                subst V
                exact q19_59
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q19_60
              · have he:V = 61:=by omega
                subst V
                exact q19_61
  · by_cases h62_124:V < 93
    · by_cases h62_93:V < 77
      · by_cases h62_77:V < 69
        · by_cases h62_69:V < 65
          · by_cases h62_65:V < 63
            · have he:V = 62:=by omega
              subst V
              exact q19_62
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q19_63
              · have he:V = 64:=by omega
                subst V
                exact q19_64
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q19_65
              · have he:V = 66:=by omega
                subst V
                exact q19_66
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q19_67
              · have he:V = 68:=by omega
                subst V
                exact q19_68
        · by_cases h69_77:V < 73
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q19_69
              · have he:V = 70:=by omega
                subst V
                exact q19_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q19_71
              · have he:V = 72:=by omega
                subst V
                exact q19_72
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q19_73
              · have he:V = 74:=by omega
                subst V
                exact q19_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q19_75
              · have he:V = 76:=by omega
                subst V
                exact q19_76
      · by_cases h77_93:V < 85
        · by_cases h77_85:V < 81
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q19_77
              · have he:V = 78:=by omega
                subst V
                exact q19_78
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q19_79
              · have he:V = 80:=by omega
                subst V
                exact q19_80
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q19_81
              · have he:V = 82:=by omega
                subst V
                exact q19_82
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q19_83
              · have he:V = 84:=by omega
                subst V
                exact q19_84
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q19_85
              · have he:V = 86:=by omega
                subst V
                exact q19_86
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q19_87
              · have he:V = 88:=by omega
                subst V
                exact q19_88
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q19_89
              · have he:V = 90:=by omega
                subst V
                exact q19_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q19_91
              · have he:V = 92:=by omega
                subst V
                exact q19_92
    · by_cases h93_124:V < 108
      · by_cases h93_108:V < 100
        · by_cases h93_100:V < 96
          · by_cases h93_96:V < 94
            · have he:V = 93:=by omega
              subst V
              exact q19_93
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q19_94
              · have he:V = 95:=by omega
                subst V
                exact q19_95
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q19_96
              · have he:V = 97:=by omega
                subst V
                exact q19_97
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q19_98
              · have he:V = 99:=by omega
                subst V
                exact q19_99
        · by_cases h100_108:V < 104
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q19_100
              · have he:V = 101:=by omega
                subst V
                exact q19_101
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q19_102
              · have he:V = 103:=by omega
                subst V
                exact q19_103
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q19_104
              · have he:V = 105:=by omega
                subst V
                exact q19_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q19_106
              · have he:V = 107:=by omega
                subst V
                exact q19_107
      · by_cases h108_124:V < 116
        · by_cases h108_116:V < 112
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q19_108
              · have he:V = 109:=by omega
                subst V
                exact q19_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q19_110
              · have he:V = 111:=by omega
                subst V
                exact q19_111
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q19_112
              · have he:V = 113:=by omega
                subst V
                exact q19_113
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q19_114
              · have he:V = 115:=by omega
                subst V
                exact q19_115
        · by_cases h116_124:V < 120
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q19_116
              · have he:V = 117:=by omega
                subst V
                exact q19_117
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q19_118
              · have he:V = 119:=by omega
                subst V
                exact q19_119
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q19_120
              · have he:V = 121:=by omega
                subst V
                exact q19_121
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q19_122
              · have he:V = 123:=by omega
                subst V
                exact q19_123
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
