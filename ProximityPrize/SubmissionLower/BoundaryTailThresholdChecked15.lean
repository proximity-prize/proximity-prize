import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked14

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q15_0:ThresholdAt 15 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 0 0 (by decide +kernel)
  | exact S 15 0 1 (by decide +kernel)
  | exact S 15 0 2 (by decide +kernel)
  | exact S 15 0 3 (by decide +kernel)
  | exact S 15 0 4 (by decide +kernel)
  | exact S 15 0 5 (by decide +kernel)
theorem q15_1:ThresholdAt 15 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 1 0 (by decide +kernel)
  | exact S 15 1 1 (by decide +kernel)
  | exact S 15 1 2 (by decide +kernel)
  | exact S 15 1 3 (by decide +kernel)
  | exact S 15 1 4 (by decide +kernel)
  | exact S 15 1 5 (by decide +kernel)
theorem q15_2:ThresholdAt 15 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 2 0 (by decide +kernel)
  | exact S 15 2 1 (by decide +kernel)
  | exact S 15 2 2 (by decide +kernel)
  | exact S 15 2 3 (by decide +kernel)
  | exact S 15 2 4 (by decide +kernel)
  | exact S 15 2 5 (by decide +kernel)
theorem q15_3:ThresholdAt 15 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 3 0 (by decide +kernel)
  | exact S 15 3 1 (by decide +kernel)
  | exact S 15 3 2 (by decide +kernel)
  | exact S 15 3 3 (by decide +kernel)
  | exact S 15 3 4 (by decide +kernel)
  | exact S 15 3 5 (by decide +kernel)
theorem q15_4:ThresholdAt 15 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 4 0 (by decide +kernel)
  | exact S 15 4 1 (by decide +kernel)
  | exact S 15 4 2 (by decide +kernel)
  | exact S 15 4 3 (by decide +kernel)
  | exact S 15 4 4 (by decide +kernel)
  | exact S 15 4 5 (by decide +kernel)
theorem q15_5:ThresholdAt 15 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 5 0 (by decide +kernel)
  | exact S 15 5 1 (by decide +kernel)
  | exact S 15 5 2 (by decide +kernel)
  | exact S 15 5 3 (by decide +kernel)
  | exact S 15 5 4 (by decide +kernel)
  | exact S 15 5 5 (by decide +kernel)
theorem q15_6:ThresholdAt 15 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 6 0 (by decide +kernel)
  | exact S 15 6 1 (by decide +kernel)
  | exact S 15 6 2 (by decide +kernel)
  | exact S 15 6 3 (by decide +kernel)
  | exact S 15 6 4 (by decide +kernel)
  | exact S 15 6 5 (by decide +kernel)
theorem q15_7:ThresholdAt 15 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 7 0 (by decide +kernel)
  | exact S 15 7 1 (by decide +kernel)
  | exact S 15 7 2 (by decide +kernel)
  | exact S 15 7 3 (by decide +kernel)
  | exact S 15 7 4 (by decide +kernel)
  | exact S 15 7 5 (by decide +kernel)
theorem q15_8:ThresholdAt 15 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 8 0 (by decide +kernel)
  | exact S 15 8 1 (by decide +kernel)
  | exact S 15 8 2 (by decide +kernel)
  | exact S 15 8 3 (by decide +kernel)
  | exact S 15 8 4 (by decide +kernel)
  | exact S 15 8 5 (by decide +kernel)
theorem q15_9:ThresholdAt 15 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 9 0 (by decide +kernel)
  | exact S 15 9 1 (by decide +kernel)
  | exact S 15 9 2 (by decide +kernel)
  | exact S 15 9 3 (by decide +kernel)
  | exact S 15 9 4 (by decide +kernel)
  | exact S 15 9 5 (by decide +kernel)
theorem q15_10:ThresholdAt 15 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 10 0 (by decide +kernel)
  | exact S 15 10 1 (by decide +kernel)
  | exact S 15 10 2 (by decide +kernel)
  | exact S 15 10 3 (by decide +kernel)
  | exact S 15 10 4 (by decide +kernel)
  | exact S 15 10 5 (by decide +kernel)
theorem q15_11:ThresholdAt 15 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 11 0 (by decide +kernel)
  | exact S 15 11 1 (by decide +kernel)
  | exact S 15 11 2 (by decide +kernel)
  | exact S 15 11 3 (by decide +kernel)
  | exact S 15 11 4 (by decide +kernel)
  | exact S 15 11 5 (by decide +kernel)
theorem q15_12:ThresholdAt 15 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 12 0 (by decide +kernel)
  | exact S 15 12 1 (by decide +kernel)
  | exact S 15 12 2 (by decide +kernel)
  | exact S 15 12 3 (by decide +kernel)
  | exact S 15 12 4 (by decide +kernel)
  | exact S 15 12 5 (by decide +kernel)
theorem q15_13:ThresholdAt 15 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 13 0 (by decide +kernel)
  | exact S 15 13 1 (by decide +kernel)
  | exact S 15 13 2 (by decide +kernel)
  | exact S 15 13 3 (by decide +kernel)
  | exact S 15 13 4 (by decide +kernel)
  | exact S 15 13 5 (by decide +kernel)
theorem q15_14:ThresholdAt 15 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 14 0 (by decide +kernel)
  | exact S 15 14 1 (by decide +kernel)
  | exact S 15 14 2 (by decide +kernel)
  | exact S 15 14 3 (by decide +kernel)
  | exact S 15 14 4 (by decide +kernel)
  | exact S 15 14 5 (by decide +kernel)
theorem q15_15:ThresholdAt 15 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 15 0 (by decide +kernel)
  | exact S 15 15 1 (by decide +kernel)
  | exact S 15 15 2 (by decide +kernel)
  | exact S 15 15 3 (by decide +kernel)
  | exact S 15 15 4 (by decide +kernel)
  | exact S 15 15 5 (by decide +kernel)
theorem q15_16:ThresholdAt 15 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 16 0 (by decide +kernel)
  | exact S 15 16 1 (by decide +kernel)
  | exact S 15 16 2 (by decide +kernel)
  | exact S 15 16 3 (by decide +kernel)
  | exact S 15 16 4 (by decide +kernel)
  | exact S 15 16 5 (by decide +kernel)
theorem q15_17:ThresholdAt 15 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 17 0 (by decide +kernel)
  | exact S 15 17 1 (by decide +kernel)
  | exact S 15 17 2 (by decide +kernel)
  | exact S 15 17 3 (by decide +kernel)
  | exact S 15 17 4 (by decide +kernel)
  | exact S 15 17 5 (by decide +kernel)
theorem q15_18:ThresholdAt 15 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 18 0 (by decide +kernel)
  | exact S 15 18 1 (by decide +kernel)
  | exact S 15 18 2 (by decide +kernel)
  | exact S 15 18 3 (by decide +kernel)
  | exact S 15 18 4 (by decide +kernel)
  | exact S 15 18 5 (by decide +kernel)
theorem q15_19:ThresholdAt 15 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 19 0 (by decide +kernel)
  | exact S 15 19 1 (by decide +kernel)
  | exact S 15 19 2 (by decide +kernel)
  | exact S 15 19 3 (by decide +kernel)
  | exact S 15 19 4 (by decide +kernel)
  | exact S 15 19 5 (by decide +kernel)
theorem q15_20:ThresholdAt 15 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 20 0 (by decide +kernel)
  | exact S 15 20 1 (by decide +kernel)
  | exact S 15 20 2 (by decide +kernel)
  | exact S 15 20 3 (by decide +kernel)
  | exact S 15 20 4 (by decide +kernel)
  | exact S 15 20 5 (by decide +kernel)
theorem q15_21:ThresholdAt 15 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 21 0 (by decide +kernel)
  | exact S 15 21 1 (by decide +kernel)
  | exact S 15 21 2 (by decide +kernel)
  | exact S 15 21 3 (by decide +kernel)
  | exact S 15 21 4 (by decide +kernel)
  | exact S 15 21 5 (by decide +kernel)
theorem q15_22:ThresholdAt 15 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 22 0 (by decide +kernel)
  | exact S 15 22 1 (by decide +kernel)
  | exact S 15 22 2 (by decide +kernel)
  | exact S 15 22 3 (by decide +kernel)
  | exact S 15 22 4 (by decide +kernel)
  | exact S 15 22 5 (by decide +kernel)
theorem q15_23:ThresholdAt 15 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 23 0 (by decide +kernel)
  | exact S 15 23 1 (by decide +kernel)
  | exact S 15 23 2 (by decide +kernel)
  | exact S 15 23 3 (by decide +kernel)
  | exact S 15 23 4 (by decide +kernel)
  | exact S 15 23 5 (by decide +kernel)
theorem q15_24:ThresholdAt 15 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 24 0 (by decide +kernel)
  | exact S 15 24 1 (by decide +kernel)
  | exact S 15 24 2 (by decide +kernel)
  | exact S 15 24 3 (by decide +kernel)
  | exact S 15 24 4 (by decide +kernel)
  | exact S 15 24 5 (by decide +kernel)
theorem q15_25:ThresholdAt 15 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 25 0 (by decide +kernel)
  | exact S 15 25 1 (by decide +kernel)
  | exact S 15 25 2 (by decide +kernel)
  | exact S 15 25 3 (by decide +kernel)
  | exact S 15 25 4 (by decide +kernel)
  | exact S 15 25 5 (by decide +kernel)
theorem q15_26:ThresholdAt 15 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 26 0 (by decide +kernel)
  | exact S 15 26 1 (by decide +kernel)
  | exact S 15 26 2 (by decide +kernel)
  | exact S 15 26 3 (by decide +kernel)
  | exact S 15 26 4 (by decide +kernel)
  | exact S 15 26 5 (by decide +kernel)
theorem q15_27:ThresholdAt 15 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 27 0 (by decide +kernel)
  | exact S 15 27 1 (by decide +kernel)
  | exact S 15 27 2 (by decide +kernel)
  | exact S 15 27 3 (by decide +kernel)
  | exact S 15 27 4 (by decide +kernel)
  | exact S 15 27 5 (by decide +kernel)
theorem q15_28:ThresholdAt 15 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 28 0 (by decide +kernel)
  | exact S 15 28 1 (by decide +kernel)
  | exact S 15 28 2 (by decide +kernel)
  | exact S 15 28 3 (by decide +kernel)
  | exact S 15 28 4 (by decide +kernel)
  | exact S 15 28 5 (by decide +kernel)
theorem q15_29:ThresholdAt 15 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 29 0 (by decide +kernel)
  | exact S 15 29 1 (by decide +kernel)
  | exact S 15 29 2 (by decide +kernel)
  | exact S 15 29 3 (by decide +kernel)
  | exact S 15 29 4 (by decide +kernel)
  | exact S 15 29 5 (by decide +kernel)
theorem q15_30:ThresholdAt 15 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 30 0 (by decide +kernel)
  | exact S 15 30 1 (by decide +kernel)
  | exact S 15 30 2 (by decide +kernel)
  | exact S 15 30 3 (by decide +kernel)
  | exact S 15 30 4 (by decide +kernel)
  | exact S 15 30 5 (by decide +kernel)
theorem q15_31:ThresholdAt 15 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 31 0 (by decide +kernel)
  | exact S 15 31 1 (by decide +kernel)
  | exact S 15 31 2 (by decide +kernel)
  | exact S 15 31 3 (by decide +kernel)
  | exact S 15 31 4 (by decide +kernel)
  | exact S 15 31 5 (by decide +kernel)
theorem q15_32:ThresholdAt 15 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 32 0 (by decide +kernel)
  | exact S 15 32 1 (by decide +kernel)
  | exact S 15 32 2 (by decide +kernel)
  | exact S 15 32 3 (by decide +kernel)
  | exact S 15 32 4 (by decide +kernel)
  | exact S 15 32 5 (by decide +kernel)
theorem q15_33:ThresholdAt 15 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 33 0 (by decide +kernel)
  | exact S 15 33 1 (by decide +kernel)
  | exact S 15 33 2 (by decide +kernel)
  | exact S 15 33 3 (by decide +kernel)
  | exact S 15 33 4 (by decide +kernel)
  | exact S 15 33 5 (by decide +kernel)
theorem q15_34:ThresholdAt 15 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 34 0 (by decide +kernel)
  | exact S 15 34 1 (by decide +kernel)
  | exact S 15 34 2 (by decide +kernel)
  | exact S 15 34 3 (by decide +kernel)
  | exact S 15 34 4 (by decide +kernel)
  | exact S 15 34 5 (by decide +kernel)
theorem q15_35:ThresholdAt 15 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 35 0 (by decide +kernel)
  | exact S 15 35 1 (by decide +kernel)
  | exact S 15 35 2 (by decide +kernel)
  | exact S 15 35 3 (by decide +kernel)
  | exact S 15 35 4 (by decide +kernel)
  | exact S 15 35 5 (by decide +kernel)
theorem q15_36:ThresholdAt 15 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 36 0 (by decide +kernel)
  | exact S 15 36 1 (by decide +kernel)
  | exact S 15 36 2 (by decide +kernel)
  | exact S 15 36 3 (by decide +kernel)
  | exact S 15 36 4 (by decide +kernel)
  | exact S 15 36 5 (by decide +kernel)
theorem q15_37:ThresholdAt 15 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 37 0 (by decide +kernel)
  | exact S 15 37 1 (by decide +kernel)
  | exact S 15 37 2 (by decide +kernel)
  | exact S 15 37 3 (by decide +kernel)
  | exact S 15 37 4 (by decide +kernel)
  | exact S 15 37 5 (by decide +kernel)
theorem q15_38:ThresholdAt 15 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 38 0 (by decide +kernel)
  | exact S 15 38 1 (by decide +kernel)
  | exact S 15 38 2 (by decide +kernel)
  | exact S 15 38 3 (by decide +kernel)
  | exact S 15 38 4 (by decide +kernel)
  | exact S 15 38 5 (by decide +kernel)
theorem q15_39:ThresholdAt 15 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 39 0 (by decide +kernel)
  | exact S 15 39 1 (by decide +kernel)
  | exact S 15 39 2 (by decide +kernel)
  | exact S 15 39 3 (by decide +kernel)
  | exact S 15 39 4 (by decide +kernel)
  | exact S 15 39 5 (by decide +kernel)
theorem q15_40:ThresholdAt 15 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 40 0 (by decide +kernel)
  | exact S 15 40 1 (by decide +kernel)
  | exact S 15 40 2 (by decide +kernel)
  | exact S 15 40 3 (by decide +kernel)
  | exact S 15 40 4 (by decide +kernel)
  | exact S 15 40 5 (by decide +kernel)
theorem q15_41:ThresholdAt 15 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 41 0 (by decide +kernel)
  | exact S 15 41 1 (by decide +kernel)
  | exact S 15 41 2 (by decide +kernel)
  | exact S 15 41 3 (by decide +kernel)
  | exact S 15 41 4 (by decide +kernel)
  | exact S 15 41 5 (by decide +kernel)
theorem q15_42:ThresholdAt 15 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 42 0 (by decide +kernel)
  | exact S 15 42 1 (by decide +kernel)
  | exact S 15 42 2 (by decide +kernel)
  | exact S 15 42 3 (by decide +kernel)
  | exact S 15 42 4 (by decide +kernel)
  | exact S 15 42 5 (by decide +kernel)
theorem q15_43:ThresholdAt 15 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 43 0 (by decide +kernel)
  | exact S 15 43 1 (by decide +kernel)
  | exact S 15 43 2 (by decide +kernel)
  | exact S 15 43 3 (by decide +kernel)
  | exact S 15 43 4 (by decide +kernel)
  | exact S 15 43 5 (by decide +kernel)
theorem q15_44:ThresholdAt 15 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 44 0 (by decide +kernel)
  | exact S 15 44 1 (by decide +kernel)
  | exact S 15 44 2 (by decide +kernel)
  | exact S 15 44 3 (by decide +kernel)
  | exact S 15 44 4 (by decide +kernel)
  | exact S 15 44 5 (by decide +kernel)
theorem q15_45:ThresholdAt 15 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 45 0 (by decide +kernel)
  | exact S 15 45 1 (by decide +kernel)
  | exact S 15 45 2 (by decide +kernel)
  | exact S 15 45 3 (by decide +kernel)
  | exact S 15 45 4 (by decide +kernel)
  | exact S 15 45 5 (by decide +kernel)
theorem q15_46:ThresholdAt 15 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 46 0 (by decide +kernel)
  | exact S 15 46 1 (by decide +kernel)
  | exact S 15 46 2 (by decide +kernel)
  | exact S 15 46 3 (by decide +kernel)
  | exact S 15 46 4 (by decide +kernel)
  | exact S 15 46 5 (by decide +kernel)
theorem q15_47:ThresholdAt 15 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 47 0 (by decide +kernel)
  | exact S 15 47 1 (by decide +kernel)
  | exact S 15 47 2 (by decide +kernel)
  | exact S 15 47 3 (by decide +kernel)
  | exact S 15 47 4 (by decide +kernel)
  | exact S 15 47 5 (by decide +kernel)
theorem q15_48:ThresholdAt 15 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 48 0 (by decide +kernel)
  | exact S 15 48 1 (by decide +kernel)
  | exact S 15 48 2 (by decide +kernel)
  | exact S 15 48 3 (by decide +kernel)
  | exact S 15 48 4 (by decide +kernel)
  | exact S 15 48 5 (by decide +kernel)
theorem q15_49:ThresholdAt 15 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 49 0 (by decide +kernel)
  | exact S 15 49 1 (by decide +kernel)
  | exact S 15 49 2 (by decide +kernel)
  | exact S 15 49 3 (by decide +kernel)
  | exact S 15 49 4 (by decide +kernel)
  | exact S 15 49 5 (by decide +kernel)
theorem q15_50:ThresholdAt 15 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 50 0 (by decide +kernel)
  | exact S 15 50 1 (by decide +kernel)
  | exact S 15 50 2 (by decide +kernel)
  | exact S 15 50 3 (by decide +kernel)
  | exact S 15 50 4 (by decide +kernel)
  | exact S 15 50 5 (by decide +kernel)
theorem q15_51:ThresholdAt 15 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 51 0 (by decide +kernel)
  | exact S 15 51 1 (by decide +kernel)
  | exact S 15 51 2 (by decide +kernel)
  | exact S 15 51 3 (by decide +kernel)
  | exact S 15 51 4 (by decide +kernel)
  | exact S 15 51 5 (by decide +kernel)
theorem q15_52:ThresholdAt 15 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 52 0 (by decide +kernel)
  | exact S 15 52 1 (by decide +kernel)
  | exact S 15 52 2 (by decide +kernel)
  | exact S 15 52 3 (by decide +kernel)
  | exact S 15 52 4 (by decide +kernel)
  | exact S 15 52 5 (by decide +kernel)
theorem q15_53:ThresholdAt 15 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 53 0 (by decide +kernel)
  | exact S 15 53 1 (by decide +kernel)
  | exact S 15 53 2 (by decide +kernel)
  | exact S 15 53 3 (by decide +kernel)
  | exact S 15 53 4 (by decide +kernel)
  | exact S 15 53 5 (by decide +kernel)
theorem q15_54:ThresholdAt 15 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 54 0 (by decide +kernel)
  | exact S 15 54 1 (by decide +kernel)
  | exact S 15 54 2 (by decide +kernel)
  | exact S 15 54 3 (by decide +kernel)
  | exact S 15 54 4 (by decide +kernel)
  | exact S 15 54 5 (by decide +kernel)
theorem q15_55:ThresholdAt 15 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 55 0 (by decide +kernel)
  | exact S 15 55 1 (by decide +kernel)
  | exact S 15 55 2 (by decide +kernel)
  | exact S 15 55 3 (by decide +kernel)
  | exact S 15 55 4 (by decide +kernel)
  | exact S 15 55 5 (by decide +kernel)
theorem q15_56:ThresholdAt 15 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 56 0 (by decide +kernel)
  | exact S 15 56 1 (by decide +kernel)
  | exact S 15 56 2 (by decide +kernel)
  | exact S 15 56 3 (by decide +kernel)
  | exact S 15 56 4 (by decide +kernel)
  | exact S 15 56 5 (by decide +kernel)
theorem q15_57:ThresholdAt 15 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 57 0 (by decide +kernel)
  | exact S 15 57 1 (by decide +kernel)
  | exact S 15 57 2 (by decide +kernel)
  | exact S 15 57 3 (by decide +kernel)
  | exact S 15 57 4 (by decide +kernel)
  | exact S 15 57 5 (by decide +kernel)
theorem q15_58:ThresholdAt 15 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 58 0 (by decide +kernel)
  | exact S 15 58 1 (by decide +kernel)
  | exact S 15 58 2 (by decide +kernel)
  | exact S 15 58 3 (by decide +kernel)
  | exact S 15 58 4 (by decide +kernel)
  | exact S 15 58 5 (by decide +kernel)
theorem q15_59:ThresholdAt 15 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 59 0 (by decide +kernel)
  | exact S 15 59 1 (by decide +kernel)
  | exact S 15 59 2 (by decide +kernel)
  | exact S 15 59 3 (by decide +kernel)
  | exact S 15 59 4 (by decide +kernel)
  | exact S 15 59 5 (by decide +kernel)
theorem q15_60:ThresholdAt 15 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 60 0 (by decide +kernel)
  | exact S 15 60 1 (by decide +kernel)
  | exact S 15 60 2 (by decide +kernel)
  | exact S 15 60 3 (by decide +kernel)
  | exact S 15 60 4 (by decide +kernel)
  | exact S 15 60 5 (by decide +kernel)
theorem q15_61:ThresholdAt 15 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 61 0 (by decide +kernel)
  | exact S 15 61 1 (by decide +kernel)
  | exact S 15 61 2 (by decide +kernel)
  | exact S 15 61 3 (by decide +kernel)
  | exact S 15 61 4 (by decide +kernel)
  | exact S 15 61 5 (by decide +kernel)
theorem q15_62:ThresholdAt 15 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 62 0 (by decide +kernel)
  | exact S 15 62 1 (by decide +kernel)
  | exact S 15 62 2 (by decide +kernel)
  | exact S 15 62 3 (by decide +kernel)
  | exact S 15 62 4 (by decide +kernel)
  | exact S 15 62 5 (by decide +kernel)
theorem q15_63:ThresholdAt 15 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 63 0 (by decide +kernel)
  | exact S 15 63 1 (by decide +kernel)
  | exact S 15 63 2 (by decide +kernel)
  | exact S 15 63 3 (by decide +kernel)
  | exact S 15 63 4 (by decide +kernel)
  | exact S 15 63 5 (by decide +kernel)
theorem q15_64:ThresholdAt 15 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 64 0 (by decide +kernel)
  | exact S 15 64 1 (by decide +kernel)
  | exact S 15 64 2 (by decide +kernel)
  | exact S 15 64 3 (by decide +kernel)
  | exact S 15 64 4 (by decide +kernel)
  | exact S 15 64 5 (by decide +kernel)
theorem q15_65:ThresholdAt 15 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 65 0 (by decide +kernel)
  | exact S 15 65 1 (by decide +kernel)
  | exact S 15 65 2 (by decide +kernel)
  | exact S 15 65 3 (by decide +kernel)
  | exact S 15 65 4 (by decide +kernel)
  | exact S 15 65 5 (by decide +kernel)
theorem q15_66:ThresholdAt 15 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 66 0 (by decide +kernel)
  | exact S 15 66 1 (by decide +kernel)
  | exact S 15 66 2 (by decide +kernel)
  | exact S 15 66 3 (by decide +kernel)
  | exact S 15 66 4 (by decide +kernel)
  | exact S 15 66 5 (by decide +kernel)
theorem q15_67:ThresholdAt 15 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 67 0 (by decide +kernel)
  | exact S 15 67 1 (by decide +kernel)
  | exact S 15 67 2 (by decide +kernel)
  | exact S 15 67 3 (by decide +kernel)
  | exact S 15 67 4 (by decide +kernel)
  | exact S 15 67 5 (by decide +kernel)
theorem q15_68:ThresholdAt 15 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 68 0 (by decide +kernel)
  | exact S 15 68 1 (by decide +kernel)
  | exact S 15 68 2 (by decide +kernel)
  | exact S 15 68 3 (by decide +kernel)
  | exact S 15 68 4 (by decide +kernel)
  | exact S 15 68 5 (by decide +kernel)
theorem q15_69:ThresholdAt 15 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 69 0 (by decide +kernel)
  | exact S 15 69 1 (by decide +kernel)
  | exact S 15 69 2 (by decide +kernel)
  | exact S 15 69 3 (by decide +kernel)
  | exact S 15 69 4 (by decide +kernel)
  | exact S 15 69 5 (by decide +kernel)
theorem q15_70:ThresholdAt 15 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 70 0 (by decide +kernel)
  | exact S 15 70 1 (by decide +kernel)
  | exact S 15 70 2 (by decide +kernel)
  | exact S 15 70 3 (by decide +kernel)
  | exact S 15 70 4 (by decide +kernel)
  | exact S 15 70 5 (by decide +kernel)
theorem q15_71:ThresholdAt 15 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 71 0 (by decide +kernel)
  | exact S 15 71 1 (by decide +kernel)
  | exact S 15 71 2 (by decide +kernel)
  | exact S 15 71 3 (by decide +kernel)
  | exact S 15 71 4 (by decide +kernel)
  | exact S 15 71 5 (by decide +kernel)
theorem q15_72:ThresholdAt 15 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 72 0 (by decide +kernel)
  | exact S 15 72 1 (by decide +kernel)
  | exact S 15 72 2 (by decide +kernel)
  | exact S 15 72 3 (by decide +kernel)
  | exact S 15 72 4 (by decide +kernel)
  | exact S 15 72 5 (by decide +kernel)
theorem q15_73:ThresholdAt 15 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 73 0 (by decide +kernel)
  | exact S 15 73 1 (by decide +kernel)
  | exact S 15 73 2 (by decide +kernel)
  | exact S 15 73 3 (by decide +kernel)
  | exact S 15 73 4 (by decide +kernel)
  | exact S 15 73 5 (by decide +kernel)
theorem q15_74:ThresholdAt 15 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 74 0 (by decide +kernel)
  | exact S 15 74 1 (by decide +kernel)
  | exact S 15 74 2 (by decide +kernel)
  | exact S 15 74 3 (by decide +kernel)
  | exact S 15 74 4 (by decide +kernel)
  | exact S 15 74 5 (by decide +kernel)
theorem q15_75:ThresholdAt 15 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 75 0 (by decide +kernel)
  | exact S 15 75 1 (by decide +kernel)
  | exact S 15 75 2 (by decide +kernel)
  | exact S 15 75 3 (by decide +kernel)
  | exact S 15 75 4 (by decide +kernel)
  | exact S 15 75 5 (by decide +kernel)
theorem q15_76:ThresholdAt 15 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 76 0 (by decide +kernel)
  | exact S 15 76 1 (by decide +kernel)
  | exact S 15 76 2 (by decide +kernel)
  | exact S 15 76 3 (by decide +kernel)
  | exact S 15 76 4 (by decide +kernel)
  | exact S 15 76 5 (by decide +kernel)
theorem q15_77:ThresholdAt 15 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 77 0 (by decide +kernel)
  | exact S 15 77 1 (by decide +kernel)
  | exact S 15 77 2 (by decide +kernel)
  | exact S 15 77 3 (by decide +kernel)
  | exact S 15 77 4 (by decide +kernel)
  | exact S 15 77 5 (by decide +kernel)
theorem q15_78:ThresholdAt 15 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 78 0 (by decide +kernel)
  | exact S 15 78 1 (by decide +kernel)
  | exact S 15 78 2 (by decide +kernel)
  | exact S 15 78 3 (by decide +kernel)
  | exact S 15 78 4 (by decide +kernel)
  | exact S 15 78 5 (by decide +kernel)
theorem q15_79:ThresholdAt 15 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 79 0 (by decide +kernel)
  | exact S 15 79 1 (by decide +kernel)
  | exact S 15 79 2 (by decide +kernel)
  | exact S 15 79 3 (by decide +kernel)
  | exact S 15 79 4 (by decide +kernel)
  | exact S 15 79 5 (by decide +kernel)
theorem q15_80:ThresholdAt 15 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 80 0 (by decide +kernel)
  | exact S 15 80 1 (by decide +kernel)
  | exact S 15 80 2 (by decide +kernel)
  | exact S 15 80 3 (by decide +kernel)
  | exact S 15 80 4 (by decide +kernel)
  | exact S 15 80 5 (by decide +kernel)
theorem q15_81:ThresholdAt 15 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 81 0 (by decide +kernel)
  | exact S 15 81 1 (by decide +kernel)
  | exact S 15 81 2 (by decide +kernel)
  | exact S 15 81 3 (by decide +kernel)
  | exact S 15 81 4 (by decide +kernel)
  | exact S 15 81 5 (by decide +kernel)
theorem q15_82:ThresholdAt 15 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 82 0 (by decide +kernel)
  | exact S 15 82 1 (by decide +kernel)
  | exact S 15 82 2 (by decide +kernel)
  | exact S 15 82 3 (by decide +kernel)
  | exact S 15 82 4 (by decide +kernel)
  | exact S 15 82 5 (by decide +kernel)
theorem q15_83:ThresholdAt 15 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 83 0 (by decide +kernel)
  | exact S 15 83 1 (by decide +kernel)
  | exact S 15 83 2 (by decide +kernel)
  | exact S 15 83 3 (by decide +kernel)
  | exact S 15 83 4 (by decide +kernel)
  | exact S 15 83 5 (by decide +kernel)
theorem q15_84:ThresholdAt 15 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 84 0 (by decide +kernel)
  | exact S 15 84 1 (by decide +kernel)
  | exact S 15 84 2 (by decide +kernel)
  | exact S 15 84 3 (by decide +kernel)
  | exact S 15 84 4 (by decide +kernel)
  | exact S 15 84 5 (by decide +kernel)
theorem q15_85:ThresholdAt 15 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 85 0 (by decide +kernel)
  | exact S 15 85 1 (by decide +kernel)
  | exact S 15 85 2 (by decide +kernel)
  | exact S 15 85 3 (by decide +kernel)
  | exact S 15 85 4 (by decide +kernel)
  | exact S 15 85 5 (by decide +kernel)
theorem q15_86:ThresholdAt 15 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 86 0 (by decide +kernel)
  | exact S 15 86 1 (by decide +kernel)
  | exact S 15 86 2 (by decide +kernel)
  | exact S 15 86 3 (by decide +kernel)
  | exact S 15 86 4 (by decide +kernel)
  | exact S 15 86 5 (by decide +kernel)
theorem q15_87:ThresholdAt 15 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 87 0 (by decide +kernel)
  | exact S 15 87 1 (by decide +kernel)
  | exact S 15 87 2 (by decide +kernel)
  | exact S 15 87 3 (by decide +kernel)
  | exact S 15 87 4 (by decide +kernel)
  | exact S 15 87 5 (by decide +kernel)
theorem q15_88:ThresholdAt 15 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 88 0 (by decide +kernel)
  | exact S 15 88 1 (by decide +kernel)
  | exact S 15 88 2 (by decide +kernel)
  | exact S 15 88 3 (by decide +kernel)
  | exact S 15 88 4 (by decide +kernel)
  | exact S 15 88 5 (by decide +kernel)
theorem q15_89:ThresholdAt 15 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 89 0 (by decide +kernel)
  | exact S 15 89 1 (by decide +kernel)
  | exact S 15 89 2 (by decide +kernel)
  | exact S 15 89 3 (by decide +kernel)
  | exact S 15 89 4 (by decide +kernel)
  | exact S 15 89 5 (by decide +kernel)
theorem q15_90:ThresholdAt 15 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 90 0 (by decide +kernel)
  | exact S 15 90 1 (by decide +kernel)
  | exact S 15 90 2 (by decide +kernel)
  | exact S 15 90 3 (by decide +kernel)
  | exact S 15 90 4 (by decide +kernel)
  | exact S 15 90 5 (by decide +kernel)
theorem q15_91:ThresholdAt 15 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 91 0 (by decide +kernel)
  | exact S 15 91 1 (by decide +kernel)
  | exact S 15 91 2 (by decide +kernel)
  | exact S 15 91 3 (by decide +kernel)
  | exact S 15 91 4 (by decide +kernel)
  | exact S 15 91 5 (by decide +kernel)
theorem q15_92:ThresholdAt 15 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 92 0 (by decide +kernel)
  | exact S 15 92 1 (by decide +kernel)
  | exact S 15 92 2 (by decide +kernel)
  | exact S 15 92 3 (by decide +kernel)
  | exact S 15 92 4 (by decide +kernel)
  | exact S 15 92 5 (by decide +kernel)
theorem q15_93:ThresholdAt 15 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 93 0 (by decide +kernel)
  | exact S 15 93 1 (by decide +kernel)
  | exact S 15 93 2 (by decide +kernel)
  | exact S 15 93 3 (by decide +kernel)
  | exact S 15 93 4 (by decide +kernel)
  | exact S 15 93 5 (by decide +kernel)
theorem q15_94:ThresholdAt 15 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 94 0 (by decide +kernel)
  | exact S 15 94 1 (by decide +kernel)
  | exact S 15 94 2 (by decide +kernel)
  | exact S 15 94 3 (by decide +kernel)
  | exact S 15 94 4 (by decide +kernel)
  | exact S 15 94 5 (by decide +kernel)
theorem q15_95:ThresholdAt 15 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 95 0 (by decide +kernel)
  | exact S 15 95 1 (by decide +kernel)
  | exact S 15 95 2 (by decide +kernel)
  | exact S 15 95 3 (by decide +kernel)
  | exact S 15 95 4 (by decide +kernel)
  | exact S 15 95 5 (by decide +kernel)
theorem q15_96:ThresholdAt 15 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 96 0 (by decide +kernel)
  | exact S 15 96 1 (by decide +kernel)
  | exact S 15 96 2 (by decide +kernel)
  | exact S 15 96 3 (by decide +kernel)
  | exact S 15 96 4 (by decide +kernel)
  | exact S 15 96 5 (by decide +kernel)
theorem q15_97:ThresholdAt 15 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 97 0 (by decide +kernel)
  | exact S 15 97 1 (by decide +kernel)
  | exact S 15 97 2 (by decide +kernel)
  | exact S 15 97 3 (by decide +kernel)
  | exact S 15 97 4 (by decide +kernel)
  | exact S 15 97 5 (by decide +kernel)
theorem q15_98:ThresholdAt 15 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 98 0 (by decide +kernel)
  | exact S 15 98 1 (by decide +kernel)
  | exact S 15 98 2 (by decide +kernel)
  | exact S 15 98 3 (by decide +kernel)
  | exact S 15 98 4 (by decide +kernel)
  | exact S 15 98 5 (by decide +kernel)
theorem q15_99:ThresholdAt 15 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 99 0 (by decide +kernel)
  | exact S 15 99 1 (by decide +kernel)
  | exact S 15 99 2 (by decide +kernel)
  | exact S 15 99 3 (by decide +kernel)
  | exact S 15 99 4 (by decide +kernel)
  | exact S 15 99 5 (by decide +kernel)
theorem q15_100:ThresholdAt 15 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 100 0 (by decide +kernel)
  | exact S 15 100 1 (by decide +kernel)
  | exact S 15 100 2 (by decide +kernel)
  | exact S 15 100 3 (by decide +kernel)
  | exact S 15 100 4 (by decide +kernel)
  | exact S 15 100 5 (by decide +kernel)
theorem q15_101:ThresholdAt 15 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 101 0 (by decide +kernel)
  | exact S 15 101 1 (by decide +kernel)
  | exact S 15 101 2 (by decide +kernel)
  | exact S 15 101 3 (by decide +kernel)
  | exact S 15 101 4 (by decide +kernel)
  | exact S 15 101 5 (by decide +kernel)
theorem q15_102:ThresholdAt 15 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 102 0 (by decide +kernel)
  | exact S 15 102 1 (by decide +kernel)
  | exact S 15 102 2 (by decide +kernel)
  | exact S 15 102 3 (by decide +kernel)
  | exact S 15 102 4 (by decide +kernel)
  | exact S 15 102 5 (by decide +kernel)
theorem q15_103:ThresholdAt 15 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 103 0 (by decide +kernel)
  | exact S 15 103 1 (by decide +kernel)
  | exact S 15 103 2 (by decide +kernel)
  | exact S 15 103 3 (by decide +kernel)
  | exact S 15 103 4 (by decide +kernel)
  | exact S 15 103 5 (by decide +kernel)
theorem q15_104:ThresholdAt 15 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 104 0 (by decide +kernel)
  | exact S 15 104 1 (by decide +kernel)
  | exact S 15 104 2 (by decide +kernel)
  | exact S 15 104 3 (by decide +kernel)
  | exact S 15 104 4 (by decide +kernel)
  | exact S 15 104 5 (by decide +kernel)
theorem q15_105:ThresholdAt 15 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 105 0 (by decide +kernel)
  | exact S 15 105 1 (by decide +kernel)
  | exact S 15 105 2 (by decide +kernel)
  | exact S 15 105 3 (by decide +kernel)
  | exact S 15 105 4 (by decide +kernel)
  | exact S 15 105 5 (by decide +kernel)
theorem q15_106:ThresholdAt 15 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 106 0 (by decide +kernel)
  | exact S 15 106 1 (by decide +kernel)
  | exact S 15 106 2 (by decide +kernel)
  | exact S 15 106 3 (by decide +kernel)
  | exact S 15 106 4 (by decide +kernel)
  | exact S 15 106 5 (by decide +kernel)
theorem q15_107:ThresholdAt 15 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 107 0 (by decide +kernel)
  | exact S 15 107 1 (by decide +kernel)
  | exact S 15 107 2 (by decide +kernel)
  | exact S 15 107 3 (by decide +kernel)
  | exact S 15 107 4 (by decide +kernel)
  | exact S 15 107 5 (by decide +kernel)
theorem q15_108:ThresholdAt 15 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 108 0 (by decide +kernel)
  | exact S 15 108 1 (by decide +kernel)
  | exact S 15 108 2 (by decide +kernel)
  | exact S 15 108 3 (by decide +kernel)
  | exact S 15 108 4 (by decide +kernel)
  | exact S 15 108 5 (by decide +kernel)
theorem q15_109:ThresholdAt 15 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 109 0 (by decide +kernel)
  | exact S 15 109 1 (by decide +kernel)
  | exact S 15 109 2 (by decide +kernel)
  | exact S 15 109 3 (by decide +kernel)
  | exact S 15 109 4 (by decide +kernel)
  | exact S 15 109 5 (by decide +kernel)
theorem q15_110:ThresholdAt 15 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 110 0 (by decide +kernel)
  | exact S 15 110 1 (by decide +kernel)
  | exact S 15 110 2 (by decide +kernel)
  | exact S 15 110 3 (by decide +kernel)
  | exact S 15 110 4 (by decide +kernel)
  | exact S 15 110 5 (by decide +kernel)
theorem q15_111:ThresholdAt 15 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 111 0 (by decide +kernel)
  | exact S 15 111 1 (by decide +kernel)
  | exact S 15 111 2 (by decide +kernel)
  | exact S 15 111 3 (by decide +kernel)
  | exact S 15 111 4 (by decide +kernel)
  | exact S 15 111 5 (by decide +kernel)
theorem q15_112:ThresholdAt 15 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 112 0 (by decide +kernel)
  | exact S 15 112 1 (by decide +kernel)
  | exact S 15 112 2 (by decide +kernel)
  | exact S 15 112 3 (by decide +kernel)
  | exact S 15 112 4 (by decide +kernel)
  | exact S 15 112 5 (by decide +kernel)
theorem q15_113:ThresholdAt 15 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 113 0 (by decide +kernel)
  | exact S 15 113 1 (by decide +kernel)
  | exact S 15 113 2 (by decide +kernel)
  | exact S 15 113 3 (by decide +kernel)
  | exact S 15 113 4 (by decide +kernel)
  | exact S 15 113 5 (by decide +kernel)
theorem q15_114:ThresholdAt 15 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 114 0 (by decide +kernel)
  | exact S 15 114 1 (by decide +kernel)
  | exact S 15 114 2 (by decide +kernel)
  | exact S 15 114 3 (by decide +kernel)
  | exact S 15 114 4 (by decide +kernel)
  | exact S 15 114 5 (by decide +kernel)
theorem q15_115:ThresholdAt 15 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 115 0 (by decide +kernel)
  | exact S 15 115 1 (by decide +kernel)
  | exact S 15 115 2 (by decide +kernel)
  | exact S 15 115 3 (by decide +kernel)
  | exact S 15 115 4 (by decide +kernel)
  | exact S 15 115 5 (by decide +kernel)
theorem q15_116:ThresholdAt 15 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 116 0 (by decide +kernel)
  | exact S 15 116 1 (by decide +kernel)
  | exact S 15 116 2 (by decide +kernel)
  | exact S 15 116 3 (by decide +kernel)
  | exact S 15 116 4 (by decide +kernel)
  | exact S 15 116 5 (by decide +kernel)
theorem q15_117:ThresholdAt 15 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 117 0 (by decide +kernel)
  | exact S 15 117 1 (by decide +kernel)
  | exact S 15 117 2 (by decide +kernel)
  | exact S 15 117 3 (by decide +kernel)
  | exact S 15 117 4 (by decide +kernel)
  | exact S 15 117 5 (by decide +kernel)
theorem q15_118:ThresholdAt 15 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 118 0 (by decide +kernel)
  | exact S 15 118 1 (by decide +kernel)
  | exact S 15 118 2 (by decide +kernel)
  | exact S 15 118 3 (by decide +kernel)
  | exact S 15 118 4 (by decide +kernel)
  | exact S 15 118 5 (by decide +kernel)
theorem q15_119:ThresholdAt 15 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 119 0 (by decide +kernel)
  | exact S 15 119 1 (by decide +kernel)
  | exact S 15 119 2 (by decide +kernel)
  | exact S 15 119 3 (by decide +kernel)
  | exact S 15 119 4 (by decide +kernel)
  | exact S 15 119 5 (by decide +kernel)
theorem q15_120:ThresholdAt 15 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 120 0 (by decide +kernel)
  | exact S 15 120 1 (by decide +kernel)
  | exact S 15 120 2 (by decide +kernel)
  | exact S 15 120 3 (by decide +kernel)
  | exact S 15 120 4 (by decide +kernel)
  | exact S 15 120 5 (by decide +kernel)
theorem q15_121:ThresholdAt 15 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 121 0 (by decide +kernel)
  | exact S 15 121 1 (by decide +kernel)
  | exact S 15 121 2 (by decide +kernel)
  | exact S 15 121 3 (by decide +kernel)
  | exact S 15 121 4 (by decide +kernel)
  | exact S 15 121 5 (by decide +kernel)
theorem q15_122:ThresholdAt 15 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 122 0 (by decide +kernel)
  | exact S 15 122 1 (by decide +kernel)
  | exact S 15 122 2 (by decide +kernel)
  | exact S 15 122 3 (by decide +kernel)
  | exact S 15 122 4 (by decide +kernel)
  | exact S 15 122 5 (by decide +kernel)
theorem q15_123:ThresholdAt 15 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 123 0 (by decide +kernel)
  | exact S 15 123 1 (by decide +kernel)
  | exact S 15 123 2 (by decide +kernel)
  | exact S 15 123 3 (by decide +kernel)
  | exact S 15 123 4 (by decide +kernel)
  | exact S 15 123 5 (by decide +kernel)
theorem q15_124:ThresholdAt 15 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 124 0 (by decide +kernel)
  | exact S 15 124 1 (by decide +kernel)
  | exact S 15 124 2 (by decide +kernel)
  | exact S 15 124 3 (by decide +kernel)
  | exact S 15 124 4 (by decide +kernel)
  | exact S 15 124 5 (by decide +kernel)
theorem q15_125:ThresholdAt 15 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 125 0 (by decide +kernel)
  | exact S 15 125 1 (by decide +kernel)
  | exact S 15 125 2 (by decide +kernel)
  | exact S 15 125 3 (by decide +kernel)
  | exact S 15 125 4 (by decide +kernel)
  | exact S 15 125 5 (by decide +kernel)
theorem q15_126:ThresholdAt 15 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 126 0 (by decide +kernel)
  | exact S 15 126 1 (by decide +kernel)
  | exact S 15 126 2 (by decide +kernel)
  | exact S 15 126 3 (by decide +kernel)
  | exact S 15 126 4 (by decide +kernel)
  | exact S 15 126 5 (by decide +kernel)
theorem q15_127:ThresholdAt 15 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 15 127 0 (by decide +kernel)
  | exact S 15 127 1 (by decide +kernel)
  | exact S 15 127 2 (by decide +kernel)
  | exact S 15 127 3 (by decide +kernel)
  | exact S 15 127 4 (by decide +kernel)
  | exact S 15 127 5 (by decide +kernel)
theorem checkedR15:∀ V ∈ List.range 128,ThresholdAt 15 V:=by
  intro V hV
  have hv:V < 128:=List.mem_range.mp hV
  by_cases h0_128:V < 64
  · by_cases h0_64:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q15_0
              · have he:V = 1:=by omega
                subst V
                exact q15_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q15_2
              · have he:V = 3:=by omega
                subst V
                exact q15_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q15_4
              · have he:V = 5:=by omega
                subst V
                exact q15_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q15_6
              · have he:V = 7:=by omega
                subst V
                exact q15_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q15_8
              · have he:V = 9:=by omega
                subst V
                exact q15_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q15_10
              · have he:V = 11:=by omega
                subst V
                exact q15_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q15_12
              · have he:V = 13:=by omega
                subst V
                exact q15_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q15_14
              · have he:V = 15:=by omega
                subst V
                exact q15_15
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q15_16
              · have he:V = 17:=by omega
                subst V
                exact q15_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q15_18
              · have he:V = 19:=by omega
                subst V
                exact q15_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q15_20
              · have he:V = 21:=by omega
                subst V
                exact q15_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q15_22
              · have he:V = 23:=by omega
                subst V
                exact q15_23
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q15_24
              · have he:V = 25:=by omega
                subst V
                exact q15_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q15_26
              · have he:V = 27:=by omega
                subst V
                exact q15_27
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q15_28
              · have he:V = 29:=by omega
                subst V
                exact q15_29
            · by_cases h30_32:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q15_30
              · have he:V = 31:=by omega
                subst V
                exact q15_31
    · by_cases h32_64:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have he:V = 32:=by omega
                subst V
                exact q15_32
              · have he:V = 33:=by omega
                subst V
                exact q15_33
            · by_cases h34_36:V < 35
              · have he:V = 34:=by omega
                subst V
                exact q15_34
              · have he:V = 35:=by omega
                subst V
                exact q15_35
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q15_36
              · have he:V = 37:=by omega
                subst V
                exact q15_37
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q15_38
              · have he:V = 39:=by omega
                subst V
                exact q15_39
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q15_40
              · have he:V = 41:=by omega
                subst V
                exact q15_41
            · by_cases h42_44:V < 43
              · have he:V = 42:=by omega
                subst V
                exact q15_42
              · have he:V = 43:=by omega
                subst V
                exact q15_43
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have he:V = 44:=by omega
                subst V
                exact q15_44
              · have he:V = 45:=by omega
                subst V
                exact q15_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q15_46
              · have he:V = 47:=by omega
                subst V
                exact q15_47
      · by_cases h48_64:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q15_48
              · have he:V = 49:=by omega
                subst V
                exact q15_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q15_50
              · have he:V = 51:=by omega
                subst V
                exact q15_51
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q15_52
              · have he:V = 53:=by omega
                subst V
                exact q15_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q15_54
              · have he:V = 55:=by omega
                subst V
                exact q15_55
        · by_cases h56_64:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q15_56
              · have he:V = 57:=by omega
                subst V
                exact q15_57
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q15_58
              · have he:V = 59:=by omega
                subst V
                exact q15_59
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q15_60
              · have he:V = 61:=by omega
                subst V
                exact q15_61
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q15_62
              · have he:V = 63:=by omega
                subst V
                exact q15_63
  · by_cases h64_128:V < 96
    · by_cases h64_96:V < 80
      · by_cases h64_80:V < 72
        · by_cases h64_72:V < 68
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q15_64
              · have he:V = 65:=by omega
                subst V
                exact q15_65
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q15_66
              · have he:V = 67:=by omega
                subst V
                exact q15_67
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q15_68
              · have he:V = 69:=by omega
                subst V
                exact q15_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q15_70
              · have he:V = 71:=by omega
                subst V
                exact q15_71
        · by_cases h72_80:V < 76
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q15_72
              · have he:V = 73:=by omega
                subst V
                exact q15_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q15_74
              · have he:V = 75:=by omega
                subst V
                exact q15_75
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q15_76
              · have he:V = 77:=by omega
                subst V
                exact q15_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q15_78
              · have he:V = 79:=by omega
                subst V
                exact q15_79
      · by_cases h80_96:V < 88
        · by_cases h80_88:V < 84
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q15_80
              · have he:V = 81:=by omega
                subst V
                exact q15_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q15_82
              · have he:V = 83:=by omega
                subst V
                exact q15_83
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q15_84
              · have he:V = 85:=by omega
                subst V
                exact q15_85
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q15_86
              · have he:V = 87:=by omega
                subst V
                exact q15_87
        · by_cases h88_96:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q15_88
              · have he:V = 89:=by omega
                subst V
                exact q15_89
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q15_90
              · have he:V = 91:=by omega
                subst V
                exact q15_91
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q15_92
              · have he:V = 93:=by omega
                subst V
                exact q15_93
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q15_94
              · have he:V = 95:=by omega
                subst V
                exact q15_95
    · by_cases h96_128:V < 112
      · by_cases h96_112:V < 104
        · by_cases h96_104:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q15_96
              · have he:V = 97:=by omega
                subst V
                exact q15_97
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q15_98
              · have he:V = 99:=by omega
                subst V
                exact q15_99
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q15_100
              · have he:V = 101:=by omega
                subst V
                exact q15_101
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q15_102
              · have he:V = 103:=by omega
                subst V
                exact q15_103
        · by_cases h104_112:V < 108
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q15_104
              · have he:V = 105:=by omega
                subst V
                exact q15_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q15_106
              · have he:V = 107:=by omega
                subst V
                exact q15_107
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q15_108
              · have he:V = 109:=by omega
                subst V
                exact q15_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q15_110
              · have he:V = 111:=by omega
                subst V
                exact q15_111
      · by_cases h112_128:V < 120
        · by_cases h112_120:V < 116
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q15_112
              · have he:V = 113:=by omega
                subst V
                exact q15_113
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q15_114
              · have he:V = 115:=by omega
                subst V
                exact q15_115
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q15_116
              · have he:V = 117:=by omega
                subst V
                exact q15_117
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q15_118
              · have he:V = 119:=by omega
                subst V
                exact q15_119
        · by_cases h120_128:V < 124
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q15_120
              · have he:V = 121:=by omega
                subst V
                exact q15_121
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q15_122
              · have he:V = 123:=by omega
                subst V
                exact q15_123
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q15_124
              · have he:V = 125:=by omega
                subst V
                exact q15_125
            · by_cases h126_128:V < 127
              · have he:V = 126:=by omega
                subst V
                exact q15_126
              · have he:V = 127:=by omega
                subst V
                exact q15_127
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
