import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked24

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem q25_0:ThresholdAt 25 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 0 0 (by decide +kernel)
  | exact S 25 0 1 (by decide +kernel)
  | exact S 25 0 2 (by decide +kernel)
  | exact S 25 0 3 (by decide +kernel)
  | exact S 25 0 4 (by decide +kernel)
  | exact S 25 0 5 (by decide +kernel)
theorem q25_1:ThresholdAt 25 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 1 0 (by decide +kernel)
  | exact S 25 1 1 (by decide +kernel)
  | exact S 25 1 2 (by decide +kernel)
  | exact S 25 1 3 (by decide +kernel)
  | exact S 25 1 4 (by decide +kernel)
  | exact S 25 1 5 (by decide +kernel)
theorem q25_2:ThresholdAt 25 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 2 0 (by decide +kernel)
  | exact S 25 2 1 (by decide +kernel)
  | exact S 25 2 2 (by decide +kernel)
  | exact S 25 2 3 (by decide +kernel)
  | exact S 25 2 4 (by decide +kernel)
  | exact S 25 2 5 (by decide +kernel)
theorem q25_3:ThresholdAt 25 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 3 0 (by decide +kernel)
  | exact S 25 3 1 (by decide +kernel)
  | exact S 25 3 2 (by decide +kernel)
  | exact S 25 3 3 (by decide +kernel)
  | exact S 25 3 4 (by decide +kernel)
  | exact S 25 3 5 (by decide +kernel)
theorem q25_4:ThresholdAt 25 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 4 0 (by decide +kernel)
  | exact S 25 4 1 (by decide +kernel)
  | exact S 25 4 2 (by decide +kernel)
  | exact S 25 4 3 (by decide +kernel)
  | exact S 25 4 4 (by decide +kernel)
  | exact S 25 4 5 (by decide +kernel)
theorem q25_5:ThresholdAt 25 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 5 0 (by decide +kernel)
  | exact S 25 5 1 (by decide +kernel)
  | exact S 25 5 2 (by decide +kernel)
  | exact S 25 5 3 (by decide +kernel)
  | exact S 25 5 4 (by decide +kernel)
  | exact S 25 5 5 (by decide +kernel)
theorem q25_6:ThresholdAt 25 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 6 0 (by decide +kernel)
  | exact S 25 6 1 (by decide +kernel)
  | exact S 25 6 2 (by decide +kernel)
  | exact S 25 6 3 (by decide +kernel)
  | exact S 25 6 4 (by decide +kernel)
  | exact S 25 6 5 (by decide +kernel)
theorem q25_7:ThresholdAt 25 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 7 0 (by decide +kernel)
  | exact S 25 7 1 (by decide +kernel)
  | exact S 25 7 2 (by decide +kernel)
  | exact S 25 7 3 (by decide +kernel)
  | exact S 25 7 4 (by decide +kernel)
  | exact S 25 7 5 (by decide +kernel)
theorem q25_8:ThresholdAt 25 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 8 0 (by decide +kernel)
  | exact S 25 8 1 (by decide +kernel)
  | exact S 25 8 2 (by decide +kernel)
  | exact S 25 8 3 (by decide +kernel)
  | exact S 25 8 4 (by decide +kernel)
  | exact S 25 8 5 (by decide +kernel)
theorem q25_9:ThresholdAt 25 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 9 0 (by decide +kernel)
  | exact S 25 9 1 (by decide +kernel)
  | exact S 25 9 2 (by decide +kernel)
  | exact S 25 9 3 (by decide +kernel)
  | exact S 25 9 4 (by decide +kernel)
  | exact S 25 9 5 (by decide +kernel)
theorem q25_10:ThresholdAt 25 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 10 0 (by decide +kernel)
  | exact S 25 10 1 (by decide +kernel)
  | exact S 25 10 2 (by decide +kernel)
  | exact S 25 10 3 (by decide +kernel)
  | exact S 25 10 4 (by decide +kernel)
  | exact S 25 10 5 (by decide +kernel)
theorem q25_11:ThresholdAt 25 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 11 0 (by decide +kernel)
  | exact S 25 11 1 (by decide +kernel)
  | exact S 25 11 2 (by decide +kernel)
  | exact S 25 11 3 (by decide +kernel)
  | exact S 25 11 4 (by decide +kernel)
  | exact S 25 11 5 (by decide +kernel)
theorem q25_12:ThresholdAt 25 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 12 0 (by decide +kernel)
  | exact S 25 12 1 (by decide +kernel)
  | exact S 25 12 2 (by decide +kernel)
  | exact S 25 12 3 (by decide +kernel)
  | exact S 25 12 4 (by decide +kernel)
  | exact S 25 12 5 (by decide +kernel)
theorem q25_13:ThresholdAt 25 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 13 0 (by decide +kernel)
  | exact S 25 13 1 (by decide +kernel)
  | exact S 25 13 2 (by decide +kernel)
  | exact S 25 13 3 (by decide +kernel)
  | exact S 25 13 4 (by decide +kernel)
  | exact S 25 13 5 (by decide +kernel)
theorem q25_14:ThresholdAt 25 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 14 0 (by decide +kernel)
  | exact S 25 14 1 (by decide +kernel)
  | exact S 25 14 2 (by decide +kernel)
  | exact S 25 14 3 (by decide +kernel)
  | exact S 25 14 4 (by decide +kernel)
  | exact S 25 14 5 (by decide +kernel)
theorem q25_15:ThresholdAt 25 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 15 0 (by decide +kernel)
  | exact S 25 15 1 (by decide +kernel)
  | exact S 25 15 2 (by decide +kernel)
  | exact S 25 15 3 (by decide +kernel)
  | exact S 25 15 4 (by decide +kernel)
  | exact S 25 15 5 (by decide +kernel)
theorem q25_16:ThresholdAt 25 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 16 0 (by decide +kernel)
  | exact S 25 16 1 (by decide +kernel)
  | exact S 25 16 2 (by decide +kernel)
  | exact S 25 16 3 (by decide +kernel)
  | exact S 25 16 4 (by decide +kernel)
  | exact S 25 16 5 (by decide +kernel)
theorem q25_17:ThresholdAt 25 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 17 0 (by decide +kernel)
  | exact S 25 17 1 (by decide +kernel)
  | exact S 25 17 2 (by decide +kernel)
  | exact S 25 17 3 (by decide +kernel)
  | exact S 25 17 4 (by decide +kernel)
  | exact S 25 17 5 (by decide +kernel)
theorem q25_18:ThresholdAt 25 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 18 0 (by decide +kernel)
  | exact S 25 18 1 (by decide +kernel)
  | exact S 25 18 2 (by decide +kernel)
  | exact S 25 18 3 (by decide +kernel)
  | exact S 25 18 4 (by decide +kernel)
  | exact S 25 18 5 (by decide +kernel)
theorem q25_19:ThresholdAt 25 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 19 0 (by decide +kernel)
  | exact S 25 19 1 (by decide +kernel)
  | exact S 25 19 2 (by decide +kernel)
  | exact S 25 19 3 (by decide +kernel)
  | exact S 25 19 4 (by decide +kernel)
  | exact S 25 19 5 (by decide +kernel)
theorem q25_20:ThresholdAt 25 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 20 0 (by decide +kernel)
  | exact S 25 20 1 (by decide +kernel)
  | exact S 25 20 2 (by decide +kernel)
  | exact S 25 20 3 (by decide +kernel)
  | exact S 25 20 4 (by decide +kernel)
  | exact S 25 20 5 (by decide +kernel)
theorem q25_21:ThresholdAt 25 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 21 0 (by decide +kernel)
  | exact S 25 21 1 (by decide +kernel)
  | exact S 25 21 2 (by decide +kernel)
  | exact S 25 21 3 (by decide +kernel)
  | exact S 25 21 4 (by decide +kernel)
  | exact S 25 21 5 (by decide +kernel)
theorem q25_22:ThresholdAt 25 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 22 0 (by decide +kernel)
  | exact S 25 22 1 (by decide +kernel)
  | exact S 25 22 2 (by decide +kernel)
  | exact S 25 22 3 (by decide +kernel)
  | exact S 25 22 4 (by decide +kernel)
  | exact S 25 22 5 (by decide +kernel)
theorem q25_23:ThresholdAt 25 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 23 0 (by decide +kernel)
  | exact S 25 23 1 (by decide +kernel)
  | exact S 25 23 2 (by decide +kernel)
  | exact S 25 23 3 (by decide +kernel)
  | exact S 25 23 4 (by decide +kernel)
  | exact S 25 23 5 (by decide +kernel)
theorem q25_24:ThresholdAt 25 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 24 0 (by decide +kernel)
  | exact S 25 24 1 (by decide +kernel)
  | exact S 25 24 2 (by decide +kernel)
  | exact S 25 24 3 (by decide +kernel)
  | exact S 25 24 4 (by decide +kernel)
  | exact S 25 24 5 (by decide +kernel)
theorem q25_25:ThresholdAt 25 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 25 0 (by decide +kernel)
  | exact S 25 25 1 (by decide +kernel)
  | exact S 25 25 2 (by decide +kernel)
  | exact S 25 25 3 (by decide +kernel)
  | exact S 25 25 4 (by decide +kernel)
  | exact S 25 25 5 (by decide +kernel)
theorem q25_26:ThresholdAt 25 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 26 0 (by decide +kernel)
  | exact S 25 26 1 (by decide +kernel)
  | exact S 25 26 2 (by decide +kernel)
  | exact S 25 26 3 (by decide +kernel)
  | exact S 25 26 4 (by decide +kernel)
  | exact S 25 26 5 (by decide +kernel)
theorem q25_27:ThresholdAt 25 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 27 0 (by decide +kernel)
  | exact S 25 27 1 (by decide +kernel)
  | exact S 25 27 2 (by decide +kernel)
  | exact S 25 27 3 (by decide +kernel)
  | exact S 25 27 4 (by decide +kernel)
  | exact S 25 27 5 (by decide +kernel)
theorem q25_28:ThresholdAt 25 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 28 0 (by decide +kernel)
  | exact S 25 28 1 (by decide +kernel)
  | exact S 25 28 2 (by decide +kernel)
  | exact S 25 28 3 (by decide +kernel)
  | exact S 25 28 4 (by decide +kernel)
  | exact S 25 28 5 (by decide +kernel)
theorem q25_29:ThresholdAt 25 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 29 0 (by decide +kernel)
  | exact S 25 29 1 (by decide +kernel)
  | exact S 25 29 2 (by decide +kernel)
  | exact S 25 29 3 (by decide +kernel)
  | exact S 25 29 4 (by decide +kernel)
  | exact S 25 29 5 (by decide +kernel)
theorem q25_30:ThresholdAt 25 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 30 0 (by decide +kernel)
  | exact S 25 30 1 (by decide +kernel)
  | exact S 25 30 2 (by decide +kernel)
  | exact S 25 30 3 (by decide +kernel)
  | exact S 25 30 4 (by decide +kernel)
  | exact S 25 30 5 (by decide +kernel)
theorem q25_31:ThresholdAt 25 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 31 0 (by decide +kernel)
  | exact S 25 31 1 (by decide +kernel)
  | exact S 25 31 2 (by decide +kernel)
  | exact S 25 31 3 (by decide +kernel)
  | exact S 25 31 4 (by decide +kernel)
  | exact S 25 31 5 (by decide +kernel)
theorem q25_32:ThresholdAt 25 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 32 0 (by decide +kernel)
  | exact S 25 32 1 (by decide +kernel)
  | exact S 25 32 2 (by decide +kernel)
  | exact S 25 32 3 (by decide +kernel)
  | exact S 25 32 4 (by decide +kernel)
  | exact S 25 32 5 (by decide +kernel)
theorem q25_33:ThresholdAt 25 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 33 0 (by decide +kernel)
  | exact S 25 33 1 (by decide +kernel)
  | exact S 25 33 2 (by decide +kernel)
  | exact S 25 33 3 (by decide +kernel)
  | exact S 25 33 4 (by decide +kernel)
  | exact S 25 33 5 (by decide +kernel)
theorem q25_34:ThresholdAt 25 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 34 0 (by decide +kernel)
  | exact S 25 34 1 (by decide +kernel)
  | exact S 25 34 2 (by decide +kernel)
  | exact S 25 34 3 (by decide +kernel)
  | exact S 25 34 4 (by decide +kernel)
  | exact S 25 34 5 (by decide +kernel)
theorem q25_35:ThresholdAt 25 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 35 0 (by decide +kernel)
  | exact S 25 35 1 (by decide +kernel)
  | exact S 25 35 2 (by decide +kernel)
  | exact S 25 35 3 (by decide +kernel)
  | exact S 25 35 4 (by decide +kernel)
  | exact S 25 35 5 (by decide +kernel)
theorem q25_36:ThresholdAt 25 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 36 0 (by decide +kernel)
  | exact S 25 36 1 (by decide +kernel)
  | exact S 25 36 2 (by decide +kernel)
  | exact S 25 36 3 (by decide +kernel)
  | exact S 25 36 4 (by decide +kernel)
  | exact S 25 36 5 (by decide +kernel)
theorem q25_37:ThresholdAt 25 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 37 0 (by decide +kernel)
  | exact S 25 37 1 (by decide +kernel)
  | exact S 25 37 2 (by decide +kernel)
  | exact S 25 37 3 (by decide +kernel)
  | exact S 25 37 4 (by decide +kernel)
  | exact S 25 37 5 (by decide +kernel)
theorem q25_38:ThresholdAt 25 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 38 0 (by decide +kernel)
  | exact S 25 38 1 (by decide +kernel)
  | exact S 25 38 2 (by decide +kernel)
  | exact S 25 38 3 (by decide +kernel)
  | exact S 25 38 4 (by decide +kernel)
  | exact S 25 38 5 (by decide +kernel)
theorem q25_39:ThresholdAt 25 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 39 0 (by decide +kernel)
  | exact S 25 39 1 (by decide +kernel)
  | exact S 25 39 2 (by decide +kernel)
  | exact S 25 39 3 (by decide +kernel)
  | exact S 25 39 4 (by decide +kernel)
  | exact S 25 39 5 (by decide +kernel)
theorem q25_40:ThresholdAt 25 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 40 0 (by decide +kernel)
  | exact S 25 40 1 (by decide +kernel)
  | exact S 25 40 2 (by decide +kernel)
  | exact S 25 40 3 (by decide +kernel)
  | exact S 25 40 4 (by decide +kernel)
  | exact S 25 40 5 (by decide +kernel)
theorem q25_41:ThresholdAt 25 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 41 0 (by decide +kernel)
  | exact S 25 41 1 (by decide +kernel)
  | exact S 25 41 2 (by decide +kernel)
  | exact S 25 41 3 (by decide +kernel)
  | exact S 25 41 4 (by decide +kernel)
  | exact S 25 41 5 (by decide +kernel)
theorem q25_42:ThresholdAt 25 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 42 0 (by decide +kernel)
  | exact S 25 42 1 (by decide +kernel)
  | exact S 25 42 2 (by decide +kernel)
  | exact S 25 42 3 (by decide +kernel)
  | exact S 25 42 4 (by decide +kernel)
  | exact S 25 42 5 (by decide +kernel)
theorem q25_43:ThresholdAt 25 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 43 0 (by decide +kernel)
  | exact S 25 43 1 (by decide +kernel)
  | exact S 25 43 2 (by decide +kernel)
  | exact S 25 43 3 (by decide +kernel)
  | exact S 25 43 4 (by decide +kernel)
  | exact S 25 43 5 (by decide +kernel)
theorem q25_44:ThresholdAt 25 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 44 0 (by decide +kernel)
  | exact S 25 44 1 (by decide +kernel)
  | exact S 25 44 2 (by decide +kernel)
  | exact S 25 44 3 (by decide +kernel)
  | exact S 25 44 4 (by decide +kernel)
  | exact S 25 44 5 (by decide +kernel)
theorem q25_45:ThresholdAt 25 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 45 0 (by decide +kernel)
  | exact S 25 45 1 (by decide +kernel)
  | exact S 25 45 2 (by decide +kernel)
  | exact S 25 45 3 (by decide +kernel)
  | exact S 25 45 4 (by decide +kernel)
  | exact S 25 45 5 (by decide +kernel)
theorem q25_46:ThresholdAt 25 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 46 0 (by decide +kernel)
  | exact S 25 46 1 (by decide +kernel)
  | exact S 25 46 2 (by decide +kernel)
  | exact S 25 46 3 (by decide +kernel)
  | exact S 25 46 4 (by decide +kernel)
  | exact S 25 46 5 (by decide +kernel)
theorem q25_47:ThresholdAt 25 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 47 0 (by decide +kernel)
  | exact S 25 47 1 (by decide +kernel)
  | exact S 25 47 2 (by decide +kernel)
  | exact S 25 47 3 (by decide +kernel)
  | exact S 25 47 4 (by decide +kernel)
  | exact S 25 47 5 (by decide +kernel)
theorem q25_48:ThresholdAt 25 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 48 0 (by decide +kernel)
  | exact S 25 48 1 (by decide +kernel)
  | exact S 25 48 2 (by decide +kernel)
  | exact S 25 48 3 (by decide +kernel)
  | exact S 25 48 4 (by decide +kernel)
  | exact S 25 48 5 (by decide +kernel)
theorem q25_49:ThresholdAt 25 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 49 0 (by decide +kernel)
  | exact S 25 49 1 (by decide +kernel)
  | exact S 25 49 2 (by decide +kernel)
  | exact S 25 49 3 (by decide +kernel)
  | exact S 25 49 4 (by decide +kernel)
  | exact S 25 49 5 (by decide +kernel)
theorem q25_50:ThresholdAt 25 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 50 0 (by decide +kernel)
  | exact S 25 50 1 (by decide +kernel)
  | exact S 25 50 2 (by decide +kernel)
  | exact S 25 50 3 (by decide +kernel)
  | exact S 25 50 4 (by decide +kernel)
  | exact S 25 50 5 (by decide +kernel)
theorem q25_51:ThresholdAt 25 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 51 0 (by decide +kernel)
  | exact S 25 51 1 (by decide +kernel)
  | exact S 25 51 2 (by decide +kernel)
  | exact S 25 51 3 (by decide +kernel)
  | exact S 25 51 4 (by decide +kernel)
  | exact S 25 51 5 (by decide +kernel)
theorem q25_52:ThresholdAt 25 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 52 0 (by decide +kernel)
  | exact S 25 52 1 (by decide +kernel)
  | exact S 25 52 2 (by decide +kernel)
  | exact S 25 52 3 (by decide +kernel)
  | exact S 25 52 4 (by decide +kernel)
  | exact S 25 52 5 (by decide +kernel)
theorem q25_53:ThresholdAt 25 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 53 0 (by decide +kernel)
  | exact S 25 53 1 (by decide +kernel)
  | exact S 25 53 2 (by decide +kernel)
  | exact S 25 53 3 (by decide +kernel)
  | exact S 25 53 4 (by decide +kernel)
  | exact S 25 53 5 (by decide +kernel)
theorem q25_54:ThresholdAt 25 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 54 0 (by decide +kernel)
  | exact S 25 54 1 (by decide +kernel)
  | exact S 25 54 2 (by decide +kernel)
  | exact S 25 54 3 (by decide +kernel)
  | exact S 25 54 4 (by decide +kernel)
  | exact S 25 54 5 (by decide +kernel)
theorem q25_55:ThresholdAt 25 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 55 0 (by decide +kernel)
  | exact S 25 55 1 (by decide +kernel)
  | exact S 25 55 2 (by decide +kernel)
  | exact S 25 55 3 (by decide +kernel)
  | exact S 25 55 4 (by decide +kernel)
  | exact S 25 55 5 (by decide +kernel)
theorem q25_56:ThresholdAt 25 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 56 0 (by decide +kernel)
  | exact S 25 56 1 (by decide +kernel)
  | exact S 25 56 2 (by decide +kernel)
  | exact S 25 56 3 (by decide +kernel)
  | exact S 25 56 4 (by decide +kernel)
  | exact S 25 56 5 (by decide +kernel)
theorem q25_57:ThresholdAt 25 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 57 0 (by decide +kernel)
  | exact S 25 57 1 (by decide +kernel)
  | exact S 25 57 2 (by decide +kernel)
  | exact S 25 57 3 (by decide +kernel)
  | exact S 25 57 4 (by decide +kernel)
  | exact S 25 57 5 (by decide +kernel)
theorem q25_58:ThresholdAt 25 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 58 0 (by decide +kernel)
  | exact S 25 58 1 (by decide +kernel)
  | exact S 25 58 2 (by decide +kernel)
  | exact S 25 58 3 (by decide +kernel)
  | exact S 25 58 4 (by decide +kernel)
  | exact S 25 58 5 (by decide +kernel)
theorem q25_59:ThresholdAt 25 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 59 0 (by decide +kernel)
  | exact S 25 59 1 (by decide +kernel)
  | exact S 25 59 2 (by decide +kernel)
  | exact S 25 59 3 (by decide +kernel)
  | exact S 25 59 4 (by decide +kernel)
  | exact S 25 59 5 (by decide +kernel)
theorem q25_60:ThresholdAt 25 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 60 0 (by decide +kernel)
  | exact S 25 60 1 (by decide +kernel)
  | exact S 25 60 2 (by decide +kernel)
  | exact S 25 60 3 (by decide +kernel)
  | exact S 25 60 4 (by decide +kernel)
  | exact S 25 60 5 (by decide +kernel)
theorem q25_61:ThresholdAt 25 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 61 0 (by decide +kernel)
  | exact S 25 61 1 (by decide +kernel)
  | exact S 25 61 2 (by decide +kernel)
  | exact S 25 61 3 (by decide +kernel)
  | exact S 25 61 4 (by decide +kernel)
  | exact S 25 61 5 (by decide +kernel)
theorem q25_62:ThresholdAt 25 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 62 0 (by decide +kernel)
  | exact S 25 62 1 (by decide +kernel)
  | exact S 25 62 2 (by decide +kernel)
  | exact S 25 62 3 (by decide +kernel)
  | exact S 25 62 4 (by decide +kernel)
  | exact S 25 62 5 (by decide +kernel)
theorem q25_63:ThresholdAt 25 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 63 0 (by decide +kernel)
  | exact S 25 63 1 (by decide +kernel)
  | exact S 25 63 2 (by decide +kernel)
  | exact S 25 63 3 (by decide +kernel)
  | exact S 25 63 4 (by decide +kernel)
  | exact S 25 63 5 (by decide +kernel)
theorem q25_64:ThresholdAt 25 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 64 0 (by decide +kernel)
  | exact S 25 64 1 (by decide +kernel)
  | exact S 25 64 2 (by decide +kernel)
  | exact S 25 64 3 (by decide +kernel)
  | exact S 25 64 4 (by decide +kernel)
  | exact S 25 64 5 (by decide +kernel)
theorem q25_65:ThresholdAt 25 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 65 0 (by decide +kernel)
  | exact S 25 65 1 (by decide +kernel)
  | exact S 25 65 2 (by decide +kernel)
  | exact S 25 65 3 (by decide +kernel)
  | exact S 25 65 4 (by decide +kernel)
  | exact S 25 65 5 (by decide +kernel)
theorem q25_66:ThresholdAt 25 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 66 0 (by decide +kernel)
  | exact S 25 66 1 (by decide +kernel)
  | exact S 25 66 2 (by decide +kernel)
  | exact S 25 66 3 (by decide +kernel)
  | exact S 25 66 4 (by decide +kernel)
  | exact S 25 66 5 (by decide +kernel)
theorem q25_67:ThresholdAt 25 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 67 0 (by decide +kernel)
  | exact S 25 67 1 (by decide +kernel)
  | exact S 25 67 2 (by decide +kernel)
  | exact S 25 67 3 (by decide +kernel)
  | exact S 25 67 4 (by decide +kernel)
  | exact S 25 67 5 (by decide +kernel)
theorem q25_68:ThresholdAt 25 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 68 0 (by decide +kernel)
  | exact S 25 68 1 (by decide +kernel)
  | exact S 25 68 2 (by decide +kernel)
  | exact S 25 68 3 (by decide +kernel)
  | exact S 25 68 4 (by decide +kernel)
  | exact S 25 68 5 (by decide +kernel)
theorem q25_69:ThresholdAt 25 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 69 0 (by decide +kernel)
  | exact S 25 69 1 (by decide +kernel)
  | exact S 25 69 2 (by decide +kernel)
  | exact S 25 69 3 (by decide +kernel)
  | exact S 25 69 4 (by decide +kernel)
  | exact S 25 69 5 (by decide +kernel)
theorem q25_70:ThresholdAt 25 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 70 0 (by decide +kernel)
  | exact S 25 70 1 (by decide +kernel)
  | exact S 25 70 2 (by decide +kernel)
  | exact S 25 70 3 (by decide +kernel)
  | exact S 25 70 4 (by decide +kernel)
  | exact S 25 70 5 (by decide +kernel)
theorem q25_71:ThresholdAt 25 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 71 0 (by decide +kernel)
  | exact S 25 71 1 (by decide +kernel)
  | exact S 25 71 2 (by decide +kernel)
  | exact S 25 71 3 (by decide +kernel)
  | exact S 25 71 4 (by decide +kernel)
  | exact S 25 71 5 (by decide +kernel)
theorem q25_72:ThresholdAt 25 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 72 0 (by decide +kernel)
  | exact S 25 72 1 (by decide +kernel)
  | exact S 25 72 2 (by decide +kernel)
  | exact S 25 72 3 (by decide +kernel)
  | exact S 25 72 4 (by decide +kernel)
  | exact S 25 72 5 (by decide +kernel)
theorem q25_73:ThresholdAt 25 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 73 0 (by decide +kernel)
  | exact S 25 73 1 (by decide +kernel)
  | exact S 25 73 2 (by decide +kernel)
  | exact S 25 73 3 (by decide +kernel)
  | exact S 25 73 4 (by decide +kernel)
  | exact S 25 73 5 (by decide +kernel)
theorem q25_74:ThresholdAt 25 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 74 0 (by decide +kernel)
  | exact S 25 74 1 (by decide +kernel)
  | exact S 25 74 2 (by decide +kernel)
  | exact S 25 74 3 (by decide +kernel)
  | exact S 25 74 4 (by decide +kernel)
  | exact S 25 74 5 (by decide +kernel)
theorem q25_75:ThresholdAt 25 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 75 0 (by decide +kernel)
  | exact S 25 75 1 (by decide +kernel)
  | exact S 25 75 2 (by decide +kernel)
  | exact S 25 75 3 (by decide +kernel)
  | exact S 25 75 4 (by decide +kernel)
  | exact S 25 75 5 (by decide +kernel)
theorem q25_76:ThresholdAt 25 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 76 0 (by decide +kernel)
  | exact S 25 76 1 (by decide +kernel)
  | exact S 25 76 2 (by decide +kernel)
  | exact S 25 76 3 (by decide +kernel)
  | exact S 25 76 4 (by decide +kernel)
  | exact S 25 76 5 (by decide +kernel)
theorem q25_77:ThresholdAt 25 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 77 0 (by decide +kernel)
  | exact S 25 77 1 (by decide +kernel)
  | exact S 25 77 2 (by decide +kernel)
  | exact S 25 77 3 (by decide +kernel)
  | exact S 25 77 4 (by decide +kernel)
  | exact S 25 77 5 (by decide +kernel)
theorem q25_78:ThresholdAt 25 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 78 0 (by decide +kernel)
  | exact S 25 78 1 (by decide +kernel)
  | exact S 25 78 2 (by decide +kernel)
  | exact S 25 78 3 (by decide +kernel)
  | exact S 25 78 4 (by decide +kernel)
  | exact S 25 78 5 (by decide +kernel)
theorem q25_79:ThresholdAt 25 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 79 0 (by decide +kernel)
  | exact S 25 79 1 (by decide +kernel)
  | exact S 25 79 2 (by decide +kernel)
  | exact S 25 79 3 (by decide +kernel)
  | exact S 25 79 4 (by decide +kernel)
  | exact S 25 79 5 (by decide +kernel)
theorem q25_80:ThresholdAt 25 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 80 0 (by decide +kernel)
  | exact S 25 80 1 (by decide +kernel)
  | exact S 25 80 2 (by decide +kernel)
  | exact S 25 80 3 (by decide +kernel)
  | exact S 25 80 4 (by decide +kernel)
  | exact S 25 80 5 (by decide +kernel)
theorem q25_81:ThresholdAt 25 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 81 0 (by decide +kernel)
  | exact S 25 81 1 (by decide +kernel)
  | exact S 25 81 2 (by decide +kernel)
  | exact S 25 81 3 (by decide +kernel)
  | exact S 25 81 4 (by decide +kernel)
  | exact S 25 81 5 (by decide +kernel)
theorem q25_82:ThresholdAt 25 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 82 0 (by decide +kernel)
  | exact S 25 82 1 (by decide +kernel)
  | exact S 25 82 2 (by decide +kernel)
  | exact S 25 82 3 (by decide +kernel)
  | exact S 25 82 4 (by decide +kernel)
  | exact S 25 82 5 (by decide +kernel)
theorem q25_83:ThresholdAt 25 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 83 0 (by decide +kernel)
  | exact S 25 83 1 (by decide +kernel)
  | exact S 25 83 2 (by decide +kernel)
  | exact S 25 83 3 (by decide +kernel)
  | exact S 25 83 4 (by decide +kernel)
  | exact S 25 83 5 (by decide +kernel)
theorem q25_84:ThresholdAt 25 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 84 0 (by decide +kernel)
  | exact S 25 84 1 (by decide +kernel)
  | exact S 25 84 2 (by decide +kernel)
  | exact S 25 84 3 (by decide +kernel)
  | exact S 25 84 4 (by decide +kernel)
  | exact S 25 84 5 (by decide +kernel)
theorem q25_85:ThresholdAt 25 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 85 0 (by decide +kernel)
  | exact S 25 85 1 (by decide +kernel)
  | exact S 25 85 2 (by decide +kernel)
  | exact S 25 85 3 (by decide +kernel)
  | exact S 25 85 4 (by decide +kernel)
  | exact S 25 85 5 (by decide +kernel)
theorem q25_86:ThresholdAt 25 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 86 0 (by decide +kernel)
  | exact S 25 86 1 (by decide +kernel)
  | exact S 25 86 2 (by decide +kernel)
  | exact S 25 86 3 (by decide +kernel)
  | exact S 25 86 4 (by decide +kernel)
  | exact S 25 86 5 (by decide +kernel)
theorem q25_87:ThresholdAt 25 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 87 0 (by decide +kernel)
  | exact S 25 87 1 (by decide +kernel)
  | exact S 25 87 2 (by decide +kernel)
  | exact S 25 87 3 (by decide +kernel)
  | exact S 25 87 4 (by decide +kernel)
  | exact S 25 87 5 (by decide +kernel)
theorem q25_88:ThresholdAt 25 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 88 0 (by decide +kernel)
  | exact S 25 88 1 (by decide +kernel)
  | exact S 25 88 2 (by decide +kernel)
  | exact S 25 88 3 (by decide +kernel)
  | exact S 25 88 4 (by decide +kernel)
  | exact S 25 88 5 (by decide +kernel)
theorem q25_89:ThresholdAt 25 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 89 0 (by decide +kernel)
  | exact S 25 89 1 (by decide +kernel)
  | exact S 25 89 2 (by decide +kernel)
  | exact S 25 89 3 (by decide +kernel)
  | exact S 25 89 4 (by decide +kernel)
  | exact S 25 89 5 (by decide +kernel)
theorem q25_90:ThresholdAt 25 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 90 0 (by decide +kernel)
  | exact S 25 90 1 (by decide +kernel)
  | exact S 25 90 2 (by decide +kernel)
  | exact S 25 90 3 (by decide +kernel)
  | exact S 25 90 4 (by decide +kernel)
  | exact S 25 90 5 (by decide +kernel)
theorem q25_91:ThresholdAt 25 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 91 0 (by decide +kernel)
  | exact S 25 91 1 (by decide +kernel)
  | exact S 25 91 2 (by decide +kernel)
  | exact S 25 91 3 (by decide +kernel)
  | exact S 25 91 4 (by decide +kernel)
  | exact S 25 91 5 (by decide +kernel)
theorem q25_92:ThresholdAt 25 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 92 0 (by decide +kernel)
  | exact S 25 92 1 (by decide +kernel)
  | exact S 25 92 2 (by decide +kernel)
  | exact S 25 92 3 (by decide +kernel)
  | exact S 25 92 4 (by decide +kernel)
  | exact S 25 92 5 (by decide +kernel)
theorem q25_93:ThresholdAt 25 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 93 0 (by decide +kernel)
  | exact S 25 93 1 (by decide +kernel)
  | exact S 25 93 2 (by decide +kernel)
  | exact S 25 93 3 (by decide +kernel)
  | exact S 25 93 4 (by decide +kernel)
  | exact S 25 93 5 (by decide +kernel)
theorem q25_94:ThresholdAt 25 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 94 0 (by decide +kernel)
  | exact S 25 94 1 (by decide +kernel)
  | exact S 25 94 2 (by decide +kernel)
  | exact S 25 94 3 (by decide +kernel)
  | exact S 25 94 4 (by decide +kernel)
  | exact S 25 94 5 (by decide +kernel)
theorem q25_95:ThresholdAt 25 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 95 0 (by decide +kernel)
  | exact S 25 95 1 (by decide +kernel)
  | exact S 25 95 2 (by decide +kernel)
  | exact S 25 95 3 (by decide +kernel)
  | exact S 25 95 4 (by decide +kernel)
  | exact S 25 95 5 (by decide +kernel)
theorem q25_96:ThresholdAt 25 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 96 0 (by decide +kernel)
  | exact S 25 96 1 (by decide +kernel)
  | exact S 25 96 2 (by decide +kernel)
  | exact S 25 96 3 (by decide +kernel)
  | exact S 25 96 4 (by decide +kernel)
  | exact S 25 96 5 (by decide +kernel)
theorem q25_97:ThresholdAt 25 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 97 0 (by decide +kernel)
  | exact S 25 97 1 (by decide +kernel)
  | exact S 25 97 2 (by decide +kernel)
  | exact S 25 97 3 (by decide +kernel)
  | exact S 25 97 4 (by decide +kernel)
  | exact S 25 97 5 (by decide +kernel)
theorem q25_98:ThresholdAt 25 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 98 0 (by decide +kernel)
  | exact S 25 98 1 (by decide +kernel)
  | exact S 25 98 2 (by decide +kernel)
  | exact S 25 98 3 (by decide +kernel)
  | exact S 25 98 4 (by decide +kernel)
  | exact S 25 98 5 (by decide +kernel)
theorem q25_99:ThresholdAt 25 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 99 0 (by decide +kernel)
  | exact S 25 99 1 (by decide +kernel)
  | exact S 25 99 2 (by decide +kernel)
  | exact S 25 99 3 (by decide +kernel)
  | exact S 25 99 4 (by decide +kernel)
  | exact S 25 99 5 (by decide +kernel)
theorem q25_100:ThresholdAt 25 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 100 0 (by decide +kernel)
  | exact S 25 100 1 (by decide +kernel)
  | exact S 25 100 2 (by decide +kernel)
  | exact S 25 100 3 (by decide +kernel)
  | exact S 25 100 4 (by decide +kernel)
  | exact S 25 100 5 (by decide +kernel)
theorem q25_101:ThresholdAt 25 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 101 0 (by decide +kernel)
  | exact S 25 101 1 (by decide +kernel)
  | exact S 25 101 2 (by decide +kernel)
  | exact S 25 101 3 (by decide +kernel)
  | exact S 25 101 4 (by decide +kernel)
  | exact S 25 101 5 (by decide +kernel)
theorem q25_102:ThresholdAt 25 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 102 0 (by decide +kernel)
  | exact S 25 102 1 (by decide +kernel)
  | exact S 25 102 2 (by decide +kernel)
  | exact S 25 102 3 (by decide +kernel)
  | exact S 25 102 4 (by decide +kernel)
  | exact S 25 102 5 (by decide +kernel)
theorem q25_103:ThresholdAt 25 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 103 0 (by decide +kernel)
  | exact S 25 103 1 (by decide +kernel)
  | exact S 25 103 2 (by decide +kernel)
  | exact S 25 103 3 (by decide +kernel)
  | exact S 25 103 4 (by decide +kernel)
  | exact S 25 103 5 (by decide +kernel)
theorem q25_104:ThresholdAt 25 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 104 0 (by decide +kernel)
  | exact S 25 104 1 (by decide +kernel)
  | exact S 25 104 2 (by decide +kernel)
  | exact S 25 104 3 (by decide +kernel)
  | exact S 25 104 4 (by decide +kernel)
  | exact S 25 104 5 (by decide +kernel)
theorem q25_105:ThresholdAt 25 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 105 0 (by decide +kernel)
  | exact S 25 105 1 (by decide +kernel)
  | exact S 25 105 2 (by decide +kernel)
  | exact S 25 105 3 (by decide +kernel)
  | exact S 25 105 4 (by decide +kernel)
  | exact S 25 105 5 (by decide +kernel)
theorem q25_106:ThresholdAt 25 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 106 0 (by decide +kernel)
  | exact S 25 106 1 (by decide +kernel)
  | exact S 25 106 2 (by decide +kernel)
  | exact S 25 106 3 (by decide +kernel)
  | exact S 25 106 4 (by decide +kernel)
  | exact S 25 106 5 (by decide +kernel)
theorem q25_107:ThresholdAt 25 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 107 0 (by decide +kernel)
  | exact S 25 107 1 (by decide +kernel)
  | exact S 25 107 2 (by decide +kernel)
  | exact S 25 107 3 (by decide +kernel)
  | exact S 25 107 4 (by decide +kernel)
  | exact S 25 107 5 (by decide +kernel)
theorem q25_108:ThresholdAt 25 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 108 0 (by decide +kernel)
  | exact S 25 108 1 (by decide +kernel)
  | exact S 25 108 2 (by decide +kernel)
  | exact S 25 108 3 (by decide +kernel)
  | exact S 25 108 4 (by decide +kernel)
  | exact S 25 108 5 (by decide +kernel)
theorem q25_109:ThresholdAt 25 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 109 0 (by decide +kernel)
  | exact S 25 109 1 (by decide +kernel)
  | exact S 25 109 2 (by decide +kernel)
  | exact S 25 109 3 (by decide +kernel)
  | exact S 25 109 4 (by decide +kernel)
  | exact S 25 109 5 (by decide +kernel)
theorem q25_110:ThresholdAt 25 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 110 0 (by decide +kernel)
  | exact S 25 110 1 (by decide +kernel)
  | exact S 25 110 2 (by decide +kernel)
  | exact S 25 110 3 (by decide +kernel)
  | exact S 25 110 4 (by decide +kernel)
  | exact S 25 110 5 (by decide +kernel)
theorem q25_111:ThresholdAt 25 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 111 0 (by decide +kernel)
  | exact S 25 111 1 (by decide +kernel)
  | exact S 25 111 2 (by decide +kernel)
  | exact S 25 111 3 (by decide +kernel)
  | exact S 25 111 4 (by decide +kernel)
  | exact S 25 111 5 (by decide +kernel)
theorem q25_112:ThresholdAt 25 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 112 0 (by decide +kernel)
  | exact S 25 112 1 (by decide +kernel)
  | exact S 25 112 2 (by decide +kernel)
  | exact S 25 112 3 (by decide +kernel)
  | exact S 25 112 4 (by decide +kernel)
  | exact S 25 112 5 (by decide +kernel)
theorem q25_113:ThresholdAt 25 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 113 0 (by decide +kernel)
  | exact S 25 113 1 (by decide +kernel)
  | exact S 25 113 2 (by decide +kernel)
  | exact S 25 113 3 (by decide +kernel)
  | exact S 25 113 4 (by decide +kernel)
  | exact S 25 113 5 (by decide +kernel)
theorem q25_114:ThresholdAt 25 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 114 0 (by decide +kernel)
  | exact S 25 114 1 (by decide +kernel)
  | exact S 25 114 2 (by decide +kernel)
  | exact S 25 114 3 (by decide +kernel)
  | exact S 25 114 4 (by decide +kernel)
  | exact S 25 114 5 (by decide +kernel)
theorem q25_115:ThresholdAt 25 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 115 0 (by decide +kernel)
  | exact S 25 115 1 (by decide +kernel)
  | exact S 25 115 2 (by decide +kernel)
  | exact S 25 115 3 (by decide +kernel)
  | exact S 25 115 4 (by decide +kernel)
  | exact S 25 115 5 (by decide +kernel)
theorem q25_116:ThresholdAt 25 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 116 0 (by decide +kernel)
  | exact S 25 116 1 (by decide +kernel)
  | exact S 25 116 2 (by decide +kernel)
  | exact S 25 116 3 (by decide +kernel)
  | exact S 25 116 4 (by decide +kernel)
  | exact S 25 116 5 (by decide +kernel)
theorem q25_117:ThresholdAt 25 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 117 0 (by decide +kernel)
  | exact S 25 117 1 (by decide +kernel)
  | exact S 25 117 2 (by decide +kernel)
  | exact S 25 117 3 (by decide +kernel)
  | exact S 25 117 4 (by decide +kernel)
  | exact S 25 117 5 (by decide +kernel)
theorem checkedR25:∀ V ∈ List.range 118,ThresholdAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0_118:V < 59
  · by_cases h0_59:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q25_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q25_1
              · have he:V = 2:=by omega
                subst V
                exact q25_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q25_3
              · have he:V = 4:=by omega
                subst V
                exact q25_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q25_5
              · have he:V = 6:=by omega
                subst V
                exact q25_6
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have he:V = 7:=by omega
              subst V
              exact q25_7
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q25_8
              · have he:V = 9:=by omega
                subst V
                exact q25_9
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q25_10
              · have he:V = 11:=by omega
                subst V
                exact q25_11
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q25_12
              · have he:V = 13:=by omega
                subst V
                exact q25_13
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have he:V = 14:=by omega
              subst V
              exact q25_14
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q25_15
              · have he:V = 16:=by omega
                subst V
                exact q25_16
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q25_17
              · have he:V = 18:=by omega
                subst V
                exact q25_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q25_19
              · have he:V = 20:=by omega
                subst V
                exact q25_20
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q25_21
              · have he:V = 22:=by omega
                subst V
                exact q25_22
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q25_23
              · have he:V = 24:=by omega
                subst V
                exact q25_24
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q25_25
              · have he:V = 26:=by omega
                subst V
                exact q25_26
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q25_27
              · have he:V = 28:=by omega
                subst V
                exact q25_28
    · by_cases h29_59:V < 44
      · by_cases h29_44:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have he:V = 29:=by omega
              subst V
              exact q25_29
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q25_30
              · have he:V = 31:=by omega
                subst V
                exact q25_31
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q25_32
              · have he:V = 33:=by omega
                subst V
                exact q25_33
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q25_34
              · have he:V = 35:=by omega
                subst V
                exact q25_35
        · by_cases h36_44:V < 40
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q25_36
              · have he:V = 37:=by omega
                subst V
                exact q25_37
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q25_38
              · have he:V = 39:=by omega
                subst V
                exact q25_39
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q25_40
              · have he:V = 41:=by omega
                subst V
                exact q25_41
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q25_42
              · have he:V = 43:=by omega
                subst V
                exact q25_43
      · by_cases h44_59:V < 51
        · by_cases h44_51:V < 47
          · by_cases h44_47:V < 45
            · have he:V = 44:=by omega
              subst V
              exact q25_44
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q25_45
              · have he:V = 46:=by omega
                subst V
                exact q25_46
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q25_47
              · have he:V = 48:=by omega
                subst V
                exact q25_48
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q25_49
              · have he:V = 50:=by omega
                subst V
                exact q25_50
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q25_51
              · have he:V = 52:=by omega
                subst V
                exact q25_52
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q25_53
              · have he:V = 54:=by omega
                subst V
                exact q25_54
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q25_55
              · have he:V = 56:=by omega
                subst V
                exact q25_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q25_57
              · have he:V = 58:=by omega
                subst V
                exact q25_58
  · by_cases h59_118:V < 88
    · by_cases h59_88:V < 73
      · by_cases h59_73:V < 66
        · by_cases h59_66:V < 62
          · by_cases h59_62:V < 60
            · have he:V = 59:=by omega
              subst V
              exact q25_59
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q25_60
              · have he:V = 61:=by omega
                subst V
                exact q25_61
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q25_62
              · have he:V = 63:=by omega
                subst V
                exact q25_63
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q25_64
              · have he:V = 65:=by omega
                subst V
                exact q25_65
        · by_cases h66_73:V < 69
          · by_cases h66_69:V < 67
            · have he:V = 66:=by omega
              subst V
              exact q25_66
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q25_67
              · have he:V = 68:=by omega
                subst V
                exact q25_68
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q25_69
              · have he:V = 70:=by omega
                subst V
                exact q25_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q25_71
              · have he:V = 72:=by omega
                subst V
                exact q25_72
      · by_cases h73_88:V < 80
        · by_cases h73_80:V < 76
          · by_cases h73_76:V < 74
            · have he:V = 73:=by omega
              subst V
              exact q25_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q25_74
              · have he:V = 75:=by omega
                subst V
                exact q25_75
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q25_76
              · have he:V = 77:=by omega
                subst V
                exact q25_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q25_78
              · have he:V = 79:=by omega
                subst V
                exact q25_79
        · by_cases h80_88:V < 84
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q25_80
              · have he:V = 81:=by omega
                subst V
                exact q25_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q25_82
              · have he:V = 83:=by omega
                subst V
                exact q25_83
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q25_84
              · have he:V = 85:=by omega
                subst V
                exact q25_85
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q25_86
              · have he:V = 87:=by omega
                subst V
                exact q25_87
    · by_cases h88_118:V < 103
      · by_cases h88_103:V < 95
        · by_cases h88_95:V < 91
          · by_cases h88_91:V < 89
            · have he:V = 88:=by omega
              subst V
              exact q25_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q25_89
              · have he:V = 90:=by omega
                subst V
                exact q25_90
          · by_cases h91_95:V < 93
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q25_91
              · have he:V = 92:=by omega
                subst V
                exact q25_92
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q25_93
              · have he:V = 94:=by omega
                subst V
                exact q25_94
        · by_cases h95_103:V < 99
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q25_95
              · have he:V = 96:=by omega
                subst V
                exact q25_96
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q25_97
              · have he:V = 98:=by omega
                subst V
                exact q25_98
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q25_99
              · have he:V = 100:=by omega
                subst V
                exact q25_100
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q25_101
              · have he:V = 102:=by omega
                subst V
                exact q25_102
      · by_cases h103_118:V < 110
        · by_cases h103_110:V < 106
          · by_cases h103_106:V < 104
            · have he:V = 103:=by omega
              subst V
              exact q25_103
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q25_104
              · have he:V = 105:=by omega
                subst V
                exact q25_105
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q25_106
              · have he:V = 107:=by omega
                subst V
                exact q25_107
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q25_108
              · have he:V = 109:=by omega
                subst V
                exact q25_109
        · by_cases h110_118:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q25_110
              · have he:V = 111:=by omega
                subst V
                exact q25_111
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q25_112
              · have he:V = 113:=by omega
                subst V
                exact q25_113
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q25_114
              · have he:V = 115:=by omega
                subst V
                exact q25_115
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q25_116
              · have he:V = 117:=by omega
                subst V
                exact q25_117
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
