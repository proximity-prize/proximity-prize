import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked20

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q21_0:ThresholdAt 21 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 0 0 (by decide +kernel)
 · exact S 21 0 1 (by decide +kernel)
 · exact S 21 0 2 (by decide +kernel)
 · exact S 21 0 3 (by decide +kernel)
 · exact S 21 0 4 (by decide +kernel)
 · exact S 21 0 5 (by decide +kernel)
theorem q21_1:ThresholdAt 21 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 1 0 (by decide +kernel)
 · exact S 21 1 1 (by decide +kernel)
 · exact S 21 1 2 (by decide +kernel)
 · exact S 21 1 3 (by decide +kernel)
 · exact S 21 1 4 (by decide +kernel)
 · exact S 21 1 5 (by decide +kernel)
theorem q21_2:ThresholdAt 21 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 2 0 (by decide +kernel)
 · exact S 21 2 1 (by decide +kernel)
 · exact S 21 2 2 (by decide +kernel)
 · exact S 21 2 3 (by decide +kernel)
 · exact S 21 2 4 (by decide +kernel)
 · exact S 21 2 5 (by decide +kernel)
theorem q21_3:ThresholdAt 21 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 3 0 (by decide +kernel)
 · exact S 21 3 1 (by decide +kernel)
 · exact S 21 3 2 (by decide +kernel)
 · exact S 21 3 3 (by decide +kernel)
 · exact S 21 3 4 (by decide +kernel)
 · exact S 21 3 5 (by decide +kernel)
theorem q21_4:ThresholdAt 21 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 4 0 (by decide +kernel)
 · exact S 21 4 1 (by decide +kernel)
 · exact S 21 4 2 (by decide +kernel)
 · exact S 21 4 3 (by decide +kernel)
 · exact S 21 4 4 (by decide +kernel)
 · exact S 21 4 5 (by decide +kernel)
theorem q21_5:ThresholdAt 21 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 5 0 (by decide +kernel)
 · exact S 21 5 1 (by decide +kernel)
 · exact S 21 5 2 (by decide +kernel)
 · exact S 21 5 3 (by decide +kernel)
 · exact S 21 5 4 (by decide +kernel)
 · exact S 21 5 5 (by decide +kernel)
theorem q21_6:ThresholdAt 21 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 6 0 (by decide +kernel)
 · exact S 21 6 1 (by decide +kernel)
 · exact S 21 6 2 (by decide +kernel)
 · exact S 21 6 3 (by decide +kernel)
 · exact S 21 6 4 (by decide +kernel)
 · exact S 21 6 5 (by decide +kernel)
theorem q21_7:ThresholdAt 21 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 7 0 (by decide +kernel)
 · exact S 21 7 1 (by decide +kernel)
 · exact S 21 7 2 (by decide +kernel)
 · exact S 21 7 3 (by decide +kernel)
 · exact S 21 7 4 (by decide +kernel)
 · exact S 21 7 5 (by decide +kernel)
theorem q21_8:ThresholdAt 21 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 8 0 (by decide +kernel)
 · exact S 21 8 1 (by decide +kernel)
 · exact S 21 8 2 (by decide +kernel)
 · exact S 21 8 3 (by decide +kernel)
 · exact S 21 8 4 (by decide +kernel)
 · exact S 21 8 5 (by decide +kernel)
theorem q21_9:ThresholdAt 21 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 9 0 (by decide +kernel)
 · exact S 21 9 1 (by decide +kernel)
 · exact S 21 9 2 (by decide +kernel)
 · exact S 21 9 3 (by decide +kernel)
 · exact S 21 9 4 (by decide +kernel)
 · exact S 21 9 5 (by decide +kernel)
theorem q21_10:ThresholdAt 21 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 10 0 (by decide +kernel)
 · exact S 21 10 1 (by decide +kernel)
 · exact S 21 10 2 (by decide +kernel)
 · exact S 21 10 3 (by decide +kernel)
 · exact S 21 10 4 (by decide +kernel)
 · exact S 21 10 5 (by decide +kernel)
theorem q21_11:ThresholdAt 21 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 11 0 (by decide +kernel)
 · exact S 21 11 1 (by decide +kernel)
 · exact S 21 11 2 (by decide +kernel)
 · exact S 21 11 3 (by decide +kernel)
 · exact S 21 11 4 (by decide +kernel)
 · exact S 21 11 5 (by decide +kernel)
theorem q21_12:ThresholdAt 21 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 12 0 (by decide +kernel)
 · exact S 21 12 1 (by decide +kernel)
 · exact S 21 12 2 (by decide +kernel)
 · exact S 21 12 3 (by decide +kernel)
 · exact S 21 12 4 (by decide +kernel)
 · exact S 21 12 5 (by decide +kernel)
theorem q21_13:ThresholdAt 21 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 13 0 (by decide +kernel)
 · exact S 21 13 1 (by decide +kernel)
 · exact S 21 13 2 (by decide +kernel)
 · exact S 21 13 3 (by decide +kernel)
 · exact S 21 13 4 (by decide +kernel)
 · exact S 21 13 5 (by decide +kernel)
theorem q21_14:ThresholdAt 21 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 14 0 (by decide +kernel)
 · exact S 21 14 1 (by decide +kernel)
 · exact S 21 14 2 (by decide +kernel)
 · exact S 21 14 3 (by decide +kernel)
 · exact S 21 14 4 (by decide +kernel)
 · exact S 21 14 5 (by decide +kernel)
theorem q21_15:ThresholdAt 21 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 15 0 (by decide +kernel)
 · exact S 21 15 1 (by decide +kernel)
 · exact S 21 15 2 (by decide +kernel)
 · exact S 21 15 3 (by decide +kernel)
 · exact S 21 15 4 (by decide +kernel)
 · exact S 21 15 5 (by decide +kernel)
theorem q21_16:ThresholdAt 21 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 16 0 (by decide +kernel)
 · exact S 21 16 1 (by decide +kernel)
 · exact S 21 16 2 (by decide +kernel)
 · exact S 21 16 3 (by decide +kernel)
 · exact S 21 16 4 (by decide +kernel)
 · exact S 21 16 5 (by decide +kernel)
theorem q21_17:ThresholdAt 21 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 17 0 (by decide +kernel)
 · exact S 21 17 1 (by decide +kernel)
 · exact S 21 17 2 (by decide +kernel)
 · exact S 21 17 3 (by decide +kernel)
 · exact S 21 17 4 (by decide +kernel)
 · exact S 21 17 5 (by decide +kernel)
theorem q21_18:ThresholdAt 21 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 18 0 (by decide +kernel)
 · exact S 21 18 1 (by decide +kernel)
 · exact S 21 18 2 (by decide +kernel)
 · exact S 21 18 3 (by decide +kernel)
 · exact S 21 18 4 (by decide +kernel)
 · exact S 21 18 5 (by decide +kernel)
theorem q21_19:ThresholdAt 21 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 19 0 (by decide +kernel)
 · exact S 21 19 1 (by decide +kernel)
 · exact S 21 19 2 (by decide +kernel)
 · exact S 21 19 3 (by decide +kernel)
 · exact S 21 19 4 (by decide +kernel)
 · exact S 21 19 5 (by decide +kernel)
theorem q21_20:ThresholdAt 21 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 20 0 (by decide +kernel)
 · exact S 21 20 1 (by decide +kernel)
 · exact S 21 20 2 (by decide +kernel)
 · exact S 21 20 3 (by decide +kernel)
 · exact S 21 20 4 (by decide +kernel)
 · exact S 21 20 5 (by decide +kernel)
theorem q21_21:ThresholdAt 21 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 21 0 (by decide +kernel)
 · exact S 21 21 1 (by decide +kernel)
 · exact S 21 21 2 (by decide +kernel)
 · exact S 21 21 3 (by decide +kernel)
 · exact S 21 21 4 (by decide +kernel)
 · exact S 21 21 5 (by decide +kernel)
theorem q21_22:ThresholdAt 21 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 22 0 (by decide +kernel)
 · exact S 21 22 1 (by decide +kernel)
 · exact S 21 22 2 (by decide +kernel)
 · exact S 21 22 3 (by decide +kernel)
 · exact S 21 22 4 (by decide +kernel)
 · exact S 21 22 5 (by decide +kernel)
theorem q21_23:ThresholdAt 21 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 23 0 (by decide +kernel)
 · exact S 21 23 1 (by decide +kernel)
 · exact S 21 23 2 (by decide +kernel)
 · exact S 21 23 3 (by decide +kernel)
 · exact S 21 23 4 (by decide +kernel)
 · exact S 21 23 5 (by decide +kernel)
theorem q21_24:ThresholdAt 21 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 24 0 (by decide +kernel)
 · exact S 21 24 1 (by decide +kernel)
 · exact S 21 24 2 (by decide +kernel)
 · exact S 21 24 3 (by decide +kernel)
 · exact S 21 24 4 (by decide +kernel)
 · exact S 21 24 5 (by decide +kernel)
theorem q21_25:ThresholdAt 21 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 25 0 (by decide +kernel)
 · exact S 21 25 1 (by decide +kernel)
 · exact S 21 25 2 (by decide +kernel)
 · exact S 21 25 3 (by decide +kernel)
 · exact S 21 25 4 (by decide +kernel)
 · exact S 21 25 5 (by decide +kernel)
theorem q21_26:ThresholdAt 21 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 26 0 (by decide +kernel)
 · exact S 21 26 1 (by decide +kernel)
 · exact S 21 26 2 (by decide +kernel)
 · exact S 21 26 3 (by decide +kernel)
 · exact S 21 26 4 (by decide +kernel)
 · exact S 21 26 5 (by decide +kernel)
theorem q21_27:ThresholdAt 21 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 27 0 (by decide +kernel)
 · exact S 21 27 1 (by decide +kernel)
 · exact S 21 27 2 (by decide +kernel)
 · exact S 21 27 3 (by decide +kernel)
 · exact S 21 27 4 (by decide +kernel)
 · exact S 21 27 5 (by decide +kernel)
theorem q21_28:ThresholdAt 21 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 28 0 (by decide +kernel)
 · exact S 21 28 1 (by decide +kernel)
 · exact S 21 28 2 (by decide +kernel)
 · exact S 21 28 3 (by decide +kernel)
 · exact S 21 28 4 (by decide +kernel)
 · exact S 21 28 5 (by decide +kernel)
theorem q21_29:ThresholdAt 21 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 29 0 (by decide +kernel)
 · exact S 21 29 1 (by decide +kernel)
 · exact S 21 29 2 (by decide +kernel)
 · exact S 21 29 3 (by decide +kernel)
 · exact S 21 29 4 (by decide +kernel)
 · exact S 21 29 5 (by decide +kernel)
theorem q21_30:ThresholdAt 21 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 30 0 (by decide +kernel)
 · exact S 21 30 1 (by decide +kernel)
 · exact S 21 30 2 (by decide +kernel)
 · exact S 21 30 3 (by decide +kernel)
 · exact S 21 30 4 (by decide +kernel)
 · exact S 21 30 5 (by decide +kernel)
theorem q21_31:ThresholdAt 21 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 31 0 (by decide +kernel)
 · exact S 21 31 1 (by decide +kernel)
 · exact S 21 31 2 (by decide +kernel)
 · exact S 21 31 3 (by decide +kernel)
 · exact S 21 31 4 (by decide +kernel)
 · exact S 21 31 5 (by decide +kernel)
theorem q21_32:ThresholdAt 21 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 32 0 (by decide +kernel)
 · exact S 21 32 1 (by decide +kernel)
 · exact S 21 32 2 (by decide +kernel)
 · exact S 21 32 3 (by decide +kernel)
 · exact S 21 32 4 (by decide +kernel)
 · exact S 21 32 5 (by decide +kernel)
theorem q21_33:ThresholdAt 21 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 33 0 (by decide +kernel)
 · exact S 21 33 1 (by decide +kernel)
 · exact S 21 33 2 (by decide +kernel)
 · exact S 21 33 3 (by decide +kernel)
 · exact S 21 33 4 (by decide +kernel)
 · exact S 21 33 5 (by decide +kernel)
theorem q21_34:ThresholdAt 21 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 34 0 (by decide +kernel)
 · exact S 21 34 1 (by decide +kernel)
 · exact S 21 34 2 (by decide +kernel)
 · exact S 21 34 3 (by decide +kernel)
 · exact S 21 34 4 (by decide +kernel)
 · exact S 21 34 5 (by decide +kernel)
theorem q21_35:ThresholdAt 21 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 35 0 (by decide +kernel)
 · exact S 21 35 1 (by decide +kernel)
 · exact S 21 35 2 (by decide +kernel)
 · exact S 21 35 3 (by decide +kernel)
 · exact S 21 35 4 (by decide +kernel)
 · exact S 21 35 5 (by decide +kernel)
theorem q21_36:ThresholdAt 21 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 36 0 (by decide +kernel)
 · exact S 21 36 1 (by decide +kernel)
 · exact S 21 36 2 (by decide +kernel)
 · exact S 21 36 3 (by decide +kernel)
 · exact S 21 36 4 (by decide +kernel)
 · exact S 21 36 5 (by decide +kernel)
theorem q21_37:ThresholdAt 21 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 37 0 (by decide +kernel)
 · exact S 21 37 1 (by decide +kernel)
 · exact S 21 37 2 (by decide +kernel)
 · exact S 21 37 3 (by decide +kernel)
 · exact S 21 37 4 (by decide +kernel)
 · exact S 21 37 5 (by decide +kernel)
theorem q21_38:ThresholdAt 21 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 38 0 (by decide +kernel)
 · exact S 21 38 1 (by decide +kernel)
 · exact S 21 38 2 (by decide +kernel)
 · exact S 21 38 3 (by decide +kernel)
 · exact S 21 38 4 (by decide +kernel)
 · exact S 21 38 5 (by decide +kernel)
theorem q21_39:ThresholdAt 21 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 39 0 (by decide +kernel)
 · exact S 21 39 1 (by decide +kernel)
 · exact S 21 39 2 (by decide +kernel)
 · exact S 21 39 3 (by decide +kernel)
 · exact S 21 39 4 (by decide +kernel)
 · exact S 21 39 5 (by decide +kernel)
theorem q21_40:ThresholdAt 21 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 40 0 (by decide +kernel)
 · exact S 21 40 1 (by decide +kernel)
 · exact S 21 40 2 (by decide +kernel)
 · exact S 21 40 3 (by decide +kernel)
 · exact S 21 40 4 (by decide +kernel)
 · exact S 21 40 5 (by decide +kernel)
theorem q21_41:ThresholdAt 21 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 41 0 (by decide +kernel)
 · exact S 21 41 1 (by decide +kernel)
 · exact S 21 41 2 (by decide +kernel)
 · exact S 21 41 3 (by decide +kernel)
 · exact S 21 41 4 (by decide +kernel)
 · exact S 21 41 5 (by decide +kernel)
theorem q21_42:ThresholdAt 21 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 42 0 (by decide +kernel)
 · exact S 21 42 1 (by decide +kernel)
 · exact S 21 42 2 (by decide +kernel)
 · exact S 21 42 3 (by decide +kernel)
 · exact S 21 42 4 (by decide +kernel)
 · exact S 21 42 5 (by decide +kernel)
theorem q21_43:ThresholdAt 21 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 43 0 (by decide +kernel)
 · exact S 21 43 1 (by decide +kernel)
 · exact S 21 43 2 (by decide +kernel)
 · exact S 21 43 3 (by decide +kernel)
 · exact S 21 43 4 (by decide +kernel)
 · exact S 21 43 5 (by decide +kernel)
theorem q21_44:ThresholdAt 21 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 44 0 (by decide +kernel)
 · exact S 21 44 1 (by decide +kernel)
 · exact S 21 44 2 (by decide +kernel)
 · exact S 21 44 3 (by decide +kernel)
 · exact S 21 44 4 (by decide +kernel)
 · exact S 21 44 5 (by decide +kernel)
theorem q21_45:ThresholdAt 21 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 45 0 (by decide +kernel)
 · exact S 21 45 1 (by decide +kernel)
 · exact S 21 45 2 (by decide +kernel)
 · exact S 21 45 3 (by decide +kernel)
 · exact S 21 45 4 (by decide +kernel)
 · exact S 21 45 5 (by decide +kernel)
theorem q21_46:ThresholdAt 21 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 46 0 (by decide +kernel)
 · exact S 21 46 1 (by decide +kernel)
 · exact S 21 46 2 (by decide +kernel)
 · exact S 21 46 3 (by decide +kernel)
 · exact S 21 46 4 (by decide +kernel)
 · exact S 21 46 5 (by decide +kernel)
theorem q21_47:ThresholdAt 21 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 47 0 (by decide +kernel)
 · exact S 21 47 1 (by decide +kernel)
 · exact S 21 47 2 (by decide +kernel)
 · exact S 21 47 3 (by decide +kernel)
 · exact S 21 47 4 (by decide +kernel)
 · exact S 21 47 5 (by decide +kernel)
theorem q21_48:ThresholdAt 21 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 48 0 (by decide +kernel)
 · exact S 21 48 1 (by decide +kernel)
 · exact S 21 48 2 (by decide +kernel)
 · exact S 21 48 3 (by decide +kernel)
 · exact S 21 48 4 (by decide +kernel)
 · exact S 21 48 5 (by decide +kernel)
theorem q21_49:ThresholdAt 21 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 49 0 (by decide +kernel)
 · exact S 21 49 1 (by decide +kernel)
 · exact S 21 49 2 (by decide +kernel)
 · exact S 21 49 3 (by decide +kernel)
 · exact S 21 49 4 (by decide +kernel)
 · exact S 21 49 5 (by decide +kernel)
theorem q21_50:ThresholdAt 21 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 50 0 (by decide +kernel)
 · exact S 21 50 1 (by decide +kernel)
 · exact S 21 50 2 (by decide +kernel)
 · exact S 21 50 3 (by decide +kernel)
 · exact S 21 50 4 (by decide +kernel)
 · exact S 21 50 5 (by decide +kernel)
theorem q21_51:ThresholdAt 21 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 51 0 (by decide +kernel)
 · exact S 21 51 1 (by decide +kernel)
 · exact S 21 51 2 (by decide +kernel)
 · exact S 21 51 3 (by decide +kernel)
 · exact S 21 51 4 (by decide +kernel)
 · exact S 21 51 5 (by decide +kernel)
theorem q21_52:ThresholdAt 21 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 52 0 (by decide +kernel)
 · exact S 21 52 1 (by decide +kernel)
 · exact S 21 52 2 (by decide +kernel)
 · exact S 21 52 3 (by decide +kernel)
 · exact S 21 52 4 (by decide +kernel)
 · exact S 21 52 5 (by decide +kernel)
theorem q21_53:ThresholdAt 21 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 53 0 (by decide +kernel)
 · exact S 21 53 1 (by decide +kernel)
 · exact S 21 53 2 (by decide +kernel)
 · exact S 21 53 3 (by decide +kernel)
 · exact S 21 53 4 (by decide +kernel)
 · exact S 21 53 5 (by decide +kernel)
theorem q21_54:ThresholdAt 21 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 54 0 (by decide +kernel)
 · exact S 21 54 1 (by decide +kernel)
 · exact S 21 54 2 (by decide +kernel)
 · exact S 21 54 3 (by decide +kernel)
 · exact S 21 54 4 (by decide +kernel)
 · exact S 21 54 5 (by decide +kernel)
theorem q21_55:ThresholdAt 21 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 55 0 (by decide +kernel)
 · exact S 21 55 1 (by decide +kernel)
 · exact S 21 55 2 (by decide +kernel)
 · exact S 21 55 3 (by decide +kernel)
 · exact S 21 55 4 (by decide +kernel)
 · exact S 21 55 5 (by decide +kernel)
theorem q21_56:ThresholdAt 21 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 56 0 (by decide +kernel)
 · exact S 21 56 1 (by decide +kernel)
 · exact S 21 56 2 (by decide +kernel)
 · exact S 21 56 3 (by decide +kernel)
 · exact S 21 56 4 (by decide +kernel)
 · exact S 21 56 5 (by decide +kernel)
theorem q21_57:ThresholdAt 21 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 57 0 (by decide +kernel)
 · exact S 21 57 1 (by decide +kernel)
 · exact S 21 57 2 (by decide +kernel)
 · exact S 21 57 3 (by decide +kernel)
 · exact S 21 57 4 (by decide +kernel)
 · exact S 21 57 5 (by decide +kernel)
theorem q21_58:ThresholdAt 21 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 58 0 (by decide +kernel)
 · exact S 21 58 1 (by decide +kernel)
 · exact S 21 58 2 (by decide +kernel)
 · exact S 21 58 3 (by decide +kernel)
 · exact S 21 58 4 (by decide +kernel)
 · exact S 21 58 5 (by decide +kernel)
theorem q21_59:ThresholdAt 21 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 59 0 (by decide +kernel)
 · exact S 21 59 1 (by decide +kernel)
 · exact S 21 59 2 (by decide +kernel)
 · exact S 21 59 3 (by decide +kernel)
 · exact S 21 59 4 (by decide +kernel)
 · exact S 21 59 5 (by decide +kernel)
theorem q21_60:ThresholdAt 21 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 60 0 (by decide +kernel)
 · exact S 21 60 1 (by decide +kernel)
 · exact S 21 60 2 (by decide +kernel)
 · exact S 21 60 3 (by decide +kernel)
 · exact S 21 60 4 (by decide +kernel)
 · exact S 21 60 5 (by decide +kernel)
theorem q21_61:ThresholdAt 21 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 61 0 (by decide +kernel)
 · exact S 21 61 1 (by decide +kernel)
 · exact S 21 61 2 (by decide +kernel)
 · exact S 21 61 3 (by decide +kernel)
 · exact S 21 61 4 (by decide +kernel)
 · exact S 21 61 5 (by decide +kernel)
theorem q21_62:ThresholdAt 21 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 62 0 (by decide +kernel)
 · exact S 21 62 1 (by decide +kernel)
 · exact S 21 62 2 (by decide +kernel)
 · exact S 21 62 3 (by decide +kernel)
 · exact S 21 62 4 (by decide +kernel)
 · exact S 21 62 5 (by decide +kernel)
theorem q21_63:ThresholdAt 21 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 63 0 (by decide +kernel)
 · exact S 21 63 1 (by decide +kernel)
 · exact S 21 63 2 (by decide +kernel)
 · exact S 21 63 3 (by decide +kernel)
 · exact S 21 63 4 (by decide +kernel)
 · exact S 21 63 5 (by decide +kernel)
theorem q21_64:ThresholdAt 21 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 64 0 (by decide +kernel)
 · exact S 21 64 1 (by decide +kernel)
 · exact S 21 64 2 (by decide +kernel)
 · exact S 21 64 3 (by decide +kernel)
 · exact S 21 64 4 (by decide +kernel)
 · exact S 21 64 5 (by decide +kernel)
theorem q21_65:ThresholdAt 21 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 65 0 (by decide +kernel)
 · exact S 21 65 1 (by decide +kernel)
 · exact S 21 65 2 (by decide +kernel)
 · exact S 21 65 3 (by decide +kernel)
 · exact S 21 65 4 (by decide +kernel)
 · exact S 21 65 5 (by decide +kernel)
theorem q21_66:ThresholdAt 21 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 66 0 (by decide +kernel)
 · exact S 21 66 1 (by decide +kernel)
 · exact S 21 66 2 (by decide +kernel)
 · exact S 21 66 3 (by decide +kernel)
 · exact S 21 66 4 (by decide +kernel)
 · exact S 21 66 5 (by decide +kernel)
theorem q21_67:ThresholdAt 21 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 67 0 (by decide +kernel)
 · exact S 21 67 1 (by decide +kernel)
 · exact S 21 67 2 (by decide +kernel)
 · exact S 21 67 3 (by decide +kernel)
 · exact S 21 67 4 (by decide +kernel)
 · exact S 21 67 5 (by decide +kernel)
theorem q21_68:ThresholdAt 21 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 68 0 (by decide +kernel)
 · exact S 21 68 1 (by decide +kernel)
 · exact S 21 68 2 (by decide +kernel)
 · exact S 21 68 3 (by decide +kernel)
 · exact S 21 68 4 (by decide +kernel)
 · exact S 21 68 5 (by decide +kernel)
theorem q21_69:ThresholdAt 21 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 69 0 (by decide +kernel)
 · exact S 21 69 1 (by decide +kernel)
 · exact S 21 69 2 (by decide +kernel)
 · exact S 21 69 3 (by decide +kernel)
 · exact S 21 69 4 (by decide +kernel)
 · exact S 21 69 5 (by decide +kernel)
theorem q21_70:ThresholdAt 21 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 70 0 (by decide +kernel)
 · exact S 21 70 1 (by decide +kernel)
 · exact S 21 70 2 (by decide +kernel)
 · exact S 21 70 3 (by decide +kernel)
 · exact S 21 70 4 (by decide +kernel)
 · exact S 21 70 5 (by decide +kernel)
theorem q21_71:ThresholdAt 21 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 71 0 (by decide +kernel)
 · exact S 21 71 1 (by decide +kernel)
 · exact S 21 71 2 (by decide +kernel)
 · exact S 21 71 3 (by decide +kernel)
 · exact S 21 71 4 (by decide +kernel)
 · exact S 21 71 5 (by decide +kernel)
theorem q21_72:ThresholdAt 21 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 72 0 (by decide +kernel)
 · exact S 21 72 1 (by decide +kernel)
 · exact S 21 72 2 (by decide +kernel)
 · exact S 21 72 3 (by decide +kernel)
 · exact S 21 72 4 (by decide +kernel)
 · exact S 21 72 5 (by decide +kernel)
theorem q21_73:ThresholdAt 21 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 73 0 (by decide +kernel)
 · exact S 21 73 1 (by decide +kernel)
 · exact S 21 73 2 (by decide +kernel)
 · exact S 21 73 3 (by decide +kernel)
 · exact S 21 73 4 (by decide +kernel)
 · exact S 21 73 5 (by decide +kernel)
theorem q21_74:ThresholdAt 21 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 74 0 (by decide +kernel)
 · exact S 21 74 1 (by decide +kernel)
 · exact S 21 74 2 (by decide +kernel)
 · exact S 21 74 3 (by decide +kernel)
 · exact S 21 74 4 (by decide +kernel)
 · exact S 21 74 5 (by decide +kernel)
theorem q21_75:ThresholdAt 21 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 75 0 (by decide +kernel)
 · exact S 21 75 1 (by decide +kernel)
 · exact S 21 75 2 (by decide +kernel)
 · exact S 21 75 3 (by decide +kernel)
 · exact S 21 75 4 (by decide +kernel)
 · exact S 21 75 5 (by decide +kernel)
theorem q21_76:ThresholdAt 21 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 76 0 (by decide +kernel)
 · exact S 21 76 1 (by decide +kernel)
 · exact S 21 76 2 (by decide +kernel)
 · exact S 21 76 3 (by decide +kernel)
 · exact S 21 76 4 (by decide +kernel)
 · exact S 21 76 5 (by decide +kernel)
theorem q21_77:ThresholdAt 21 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 77 0 (by decide +kernel)
 · exact S 21 77 1 (by decide +kernel)
 · exact S 21 77 2 (by decide +kernel)
 · exact S 21 77 3 (by decide +kernel)
 · exact S 21 77 4 (by decide +kernel)
 · exact S 21 77 5 (by decide +kernel)
theorem q21_78:ThresholdAt 21 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 78 0 (by decide +kernel)
 · exact S 21 78 1 (by decide +kernel)
 · exact S 21 78 2 (by decide +kernel)
 · exact S 21 78 3 (by decide +kernel)
 · exact S 21 78 4 (by decide +kernel)
 · exact S 21 78 5 (by decide +kernel)
theorem q21_79:ThresholdAt 21 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 79 0 (by decide +kernel)
 · exact S 21 79 1 (by decide +kernel)
 · exact S 21 79 2 (by decide +kernel)
 · exact S 21 79 3 (by decide +kernel)
 · exact S 21 79 4 (by decide +kernel)
 · exact S 21 79 5 (by decide +kernel)
theorem q21_80:ThresholdAt 21 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 80 0 (by decide +kernel)
 · exact S 21 80 1 (by decide +kernel)
 · exact S 21 80 2 (by decide +kernel)
 · exact S 21 80 3 (by decide +kernel)
 · exact S 21 80 4 (by decide +kernel)
 · exact S 21 80 5 (by decide +kernel)
theorem q21_81:ThresholdAt 21 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 81 0 (by decide +kernel)
 · exact S 21 81 1 (by decide +kernel)
 · exact S 21 81 2 (by decide +kernel)
 · exact S 21 81 3 (by decide +kernel)
 · exact S 21 81 4 (by decide +kernel)
 · exact S 21 81 5 (by decide +kernel)
theorem q21_82:ThresholdAt 21 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 82 0 (by decide +kernel)
 · exact S 21 82 1 (by decide +kernel)
 · exact S 21 82 2 (by decide +kernel)
 · exact S 21 82 3 (by decide +kernel)
 · exact S 21 82 4 (by decide +kernel)
 · exact S 21 82 5 (by decide +kernel)
theorem q21_83:ThresholdAt 21 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 83 0 (by decide +kernel)
 · exact S 21 83 1 (by decide +kernel)
 · exact S 21 83 2 (by decide +kernel)
 · exact S 21 83 3 (by decide +kernel)
 · exact S 21 83 4 (by decide +kernel)
 · exact S 21 83 5 (by decide +kernel)
theorem q21_84:ThresholdAt 21 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 84 0 (by decide +kernel)
 · exact S 21 84 1 (by decide +kernel)
 · exact S 21 84 2 (by decide +kernel)
 · exact S 21 84 3 (by decide +kernel)
 · exact S 21 84 4 (by decide +kernel)
 · exact S 21 84 5 (by decide +kernel)
theorem q21_85:ThresholdAt 21 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 85 0 (by decide +kernel)
 · exact S 21 85 1 (by decide +kernel)
 · exact S 21 85 2 (by decide +kernel)
 · exact S 21 85 3 (by decide +kernel)
 · exact S 21 85 4 (by decide +kernel)
 · exact S 21 85 5 (by decide +kernel)
theorem q21_86:ThresholdAt 21 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 86 0 (by decide +kernel)
 · exact S 21 86 1 (by decide +kernel)
 · exact S 21 86 2 (by decide +kernel)
 · exact S 21 86 3 (by decide +kernel)
 · exact S 21 86 4 (by decide +kernel)
 · exact S 21 86 5 (by decide +kernel)
theorem q21_87:ThresholdAt 21 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 87 0 (by decide +kernel)
 · exact S 21 87 1 (by decide +kernel)
 · exact S 21 87 2 (by decide +kernel)
 · exact S 21 87 3 (by decide +kernel)
 · exact S 21 87 4 (by decide +kernel)
 · exact S 21 87 5 (by decide +kernel)
theorem q21_88:ThresholdAt 21 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 88 0 (by decide +kernel)
 · exact S 21 88 1 (by decide +kernel)
 · exact S 21 88 2 (by decide +kernel)
 · exact S 21 88 3 (by decide +kernel)
 · exact S 21 88 4 (by decide +kernel)
 · exact S 21 88 5 (by decide +kernel)
theorem q21_89:ThresholdAt 21 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 89 0 (by decide +kernel)
 · exact S 21 89 1 (by decide +kernel)
 · exact S 21 89 2 (by decide +kernel)
 · exact S 21 89 3 (by decide +kernel)
 · exact S 21 89 4 (by decide +kernel)
 · exact S 21 89 5 (by decide +kernel)
theorem q21_90:ThresholdAt 21 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 90 0 (by decide +kernel)
 · exact S 21 90 1 (by decide +kernel)
 · exact S 21 90 2 (by decide +kernel)
 · exact S 21 90 3 (by decide +kernel)
 · exact S 21 90 4 (by decide +kernel)
 · exact S 21 90 5 (by decide +kernel)
theorem q21_91:ThresholdAt 21 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 91 0 (by decide +kernel)
 · exact S 21 91 1 (by decide +kernel)
 · exact S 21 91 2 (by decide +kernel)
 · exact S 21 91 3 (by decide +kernel)
 · exact S 21 91 4 (by decide +kernel)
 · exact S 21 91 5 (by decide +kernel)
theorem q21_92:ThresholdAt 21 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 92 0 (by decide +kernel)
 · exact S 21 92 1 (by decide +kernel)
 · exact S 21 92 2 (by decide +kernel)
 · exact S 21 92 3 (by decide +kernel)
 · exact S 21 92 4 (by decide +kernel)
 · exact S 21 92 5 (by decide +kernel)
theorem q21_93:ThresholdAt 21 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 93 0 (by decide +kernel)
 · exact S 21 93 1 (by decide +kernel)
 · exact S 21 93 2 (by decide +kernel)
 · exact S 21 93 3 (by decide +kernel)
 · exact S 21 93 4 (by decide +kernel)
 · exact S 21 93 5 (by decide +kernel)
theorem q21_94:ThresholdAt 21 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 94 0 (by decide +kernel)
 · exact S 21 94 1 (by decide +kernel)
 · exact S 21 94 2 (by decide +kernel)
 · exact S 21 94 3 (by decide +kernel)
 · exact S 21 94 4 (by decide +kernel)
 · exact S 21 94 5 (by decide +kernel)
theorem q21_95:ThresholdAt 21 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 95 0 (by decide +kernel)
 · exact S 21 95 1 (by decide +kernel)
 · exact S 21 95 2 (by decide +kernel)
 · exact S 21 95 3 (by decide +kernel)
 · exact S 21 95 4 (by decide +kernel)
 · exact S 21 95 5 (by decide +kernel)
theorem q21_96:ThresholdAt 21 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 96 0 (by decide +kernel)
 · exact S 21 96 1 (by decide +kernel)
 · exact S 21 96 2 (by decide +kernel)
 · exact S 21 96 3 (by decide +kernel)
 · exact S 21 96 4 (by decide +kernel)
 · exact S 21 96 5 (by decide +kernel)
theorem q21_97:ThresholdAt 21 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 97 0 (by decide +kernel)
 · exact S 21 97 1 (by decide +kernel)
 · exact S 21 97 2 (by decide +kernel)
 · exact S 21 97 3 (by decide +kernel)
 · exact S 21 97 4 (by decide +kernel)
 · exact S 21 97 5 (by decide +kernel)
theorem q21_98:ThresholdAt 21 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 98 0 (by decide +kernel)
 · exact S 21 98 1 (by decide +kernel)
 · exact S 21 98 2 (by decide +kernel)
 · exact S 21 98 3 (by decide +kernel)
 · exact S 21 98 4 (by decide +kernel)
 · exact S 21 98 5 (by decide +kernel)
theorem q21_99:ThresholdAt 21 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 99 0 (by decide +kernel)
 · exact S 21 99 1 (by decide +kernel)
 · exact S 21 99 2 (by decide +kernel)
 · exact S 21 99 3 (by decide +kernel)
 · exact S 21 99 4 (by decide +kernel)
 · exact S 21 99 5 (by decide +kernel)
theorem q21_100:ThresholdAt 21 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 100 0 (by decide +kernel)
 · exact S 21 100 1 (by decide +kernel)
 · exact S 21 100 2 (by decide +kernel)
 · exact S 21 100 3 (by decide +kernel)
 · exact S 21 100 4 (by decide +kernel)
 · exact S 21 100 5 (by decide +kernel)
theorem q21_101:ThresholdAt 21 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 101 0 (by decide +kernel)
 · exact S 21 101 1 (by decide +kernel)
 · exact S 21 101 2 (by decide +kernel)
 · exact S 21 101 3 (by decide +kernel)
 · exact S 21 101 4 (by decide +kernel)
 · exact S 21 101 5 (by decide +kernel)
theorem q21_102:ThresholdAt 21 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 102 0 (by decide +kernel)
 · exact S 21 102 1 (by decide +kernel)
 · exact S 21 102 2 (by decide +kernel)
 · exact S 21 102 3 (by decide +kernel)
 · exact S 21 102 4 (by decide +kernel)
 · exact S 21 102 5 (by decide +kernel)
theorem q21_103:ThresholdAt 21 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 103 0 (by decide +kernel)
 · exact S 21 103 1 (by decide +kernel)
 · exact S 21 103 2 (by decide +kernel)
 · exact S 21 103 3 (by decide +kernel)
 · exact S 21 103 4 (by decide +kernel)
 · exact S 21 103 5 (by decide +kernel)
theorem q21_104:ThresholdAt 21 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 104 0 (by decide +kernel)
 · exact S 21 104 1 (by decide +kernel)
 · exact S 21 104 2 (by decide +kernel)
 · exact S 21 104 3 (by decide +kernel)
 · exact S 21 104 4 (by decide +kernel)
 · exact S 21 104 5 (by decide +kernel)
theorem q21_105:ThresholdAt 21 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 105 0 (by decide +kernel)
 · exact S 21 105 1 (by decide +kernel)
 · exact S 21 105 2 (by decide +kernel)
 · exact S 21 105 3 (by decide +kernel)
 · exact S 21 105 4 (by decide +kernel)
 · exact S 21 105 5 (by decide +kernel)
theorem q21_106:ThresholdAt 21 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 106 0 (by decide +kernel)
 · exact S 21 106 1 (by decide +kernel)
 · exact S 21 106 2 (by decide +kernel)
 · exact S 21 106 3 (by decide +kernel)
 · exact S 21 106 4 (by decide +kernel)
 · exact S 21 106 5 (by decide +kernel)
theorem q21_107:ThresholdAt 21 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 107 0 (by decide +kernel)
 · exact S 21 107 1 (by decide +kernel)
 · exact S 21 107 2 (by decide +kernel)
 · exact S 21 107 3 (by decide +kernel)
 · exact S 21 107 4 (by decide +kernel)
 · exact S 21 107 5 (by decide +kernel)
theorem q21_108:ThresholdAt 21 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 108 0 (by decide +kernel)
 · exact S 21 108 1 (by decide +kernel)
 · exact S 21 108 2 (by decide +kernel)
 · exact S 21 108 3 (by decide +kernel)
 · exact S 21 108 4 (by decide +kernel)
 · exact S 21 108 5 (by decide +kernel)
theorem q21_109:ThresholdAt 21 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 109 0 (by decide +kernel)
 · exact S 21 109 1 (by decide +kernel)
 · exact S 21 109 2 (by decide +kernel)
 · exact S 21 109 3 (by decide +kernel)
 · exact S 21 109 4 (by decide +kernel)
 · exact S 21 109 5 (by decide +kernel)
theorem q21_110:ThresholdAt 21 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 110 0 (by decide +kernel)
 · exact S 21 110 1 (by decide +kernel)
 · exact S 21 110 2 (by decide +kernel)
 · exact S 21 110 3 (by decide +kernel)
 · exact S 21 110 4 (by decide +kernel)
 · exact S 21 110 5 (by decide +kernel)
theorem q21_111:ThresholdAt 21 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 111 0 (by decide +kernel)
 · exact S 21 111 1 (by decide +kernel)
 · exact S 21 111 2 (by decide +kernel)
 · exact S 21 111 3 (by decide +kernel)
 · exact S 21 111 4 (by decide +kernel)
 · exact S 21 111 5 (by decide +kernel)
theorem q21_112:ThresholdAt 21 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 112 0 (by decide +kernel)
 · exact S 21 112 1 (by decide +kernel)
 · exact S 21 112 2 (by decide +kernel)
 · exact S 21 112 3 (by decide +kernel)
 · exact S 21 112 4 (by decide +kernel)
 · exact S 21 112 5 (by decide +kernel)
theorem q21_113:ThresholdAt 21 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 113 0 (by decide +kernel)
 · exact S 21 113 1 (by decide +kernel)
 · exact S 21 113 2 (by decide +kernel)
 · exact S 21 113 3 (by decide +kernel)
 · exact S 21 113 4 (by decide +kernel)
 · exact S 21 113 5 (by decide +kernel)
theorem q21_114:ThresholdAt 21 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 114 0 (by decide +kernel)
 · exact S 21 114 1 (by decide +kernel)
 · exact S 21 114 2 (by decide +kernel)
 · exact S 21 114 3 (by decide +kernel)
 · exact S 21 114 4 (by decide +kernel)
 · exact S 21 114 5 (by decide +kernel)
theorem q21_115:ThresholdAt 21 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 115 0 (by decide +kernel)
 · exact S 21 115 1 (by decide +kernel)
 · exact S 21 115 2 (by decide +kernel)
 · exact S 21 115 3 (by decide +kernel)
 · exact S 21 115 4 (by decide +kernel)
 · exact S 21 115 5 (by decide +kernel)
theorem q21_116:ThresholdAt 21 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 116 0 (by decide +kernel)
 · exact S 21 116 1 (by decide +kernel)
 · exact S 21 116 2 (by decide +kernel)
 · exact S 21 116 3 (by decide +kernel)
 · exact S 21 116 4 (by decide +kernel)
 · exact S 21 116 5 (by decide +kernel)
theorem q21_117:ThresholdAt 21 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 117 0 (by decide +kernel)
 · exact S 21 117 1 (by decide +kernel)
 · exact S 21 117 2 (by decide +kernel)
 · exact S 21 117 3 (by decide +kernel)
 · exact S 21 117 4 (by decide +kernel)
 · exact S 21 117 5 (by decide +kernel)
theorem q21_118:ThresholdAt 21 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 118 0 (by decide +kernel)
 · exact S 21 118 1 (by decide +kernel)
 · exact S 21 118 2 (by decide +kernel)
 · exact S 21 118 3 (by decide +kernel)
 · exact S 21 118 4 (by decide +kernel)
 · exact S 21 118 5 (by decide +kernel)
theorem q21_119:ThresholdAt 21 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 119 0 (by decide +kernel)
 · exact S 21 119 1 (by decide +kernel)
 · exact S 21 119 2 (by decide +kernel)
 · exact S 21 119 3 (by decide +kernel)
 · exact S 21 119 4 (by decide +kernel)
 · exact S 21 119 5 (by decide +kernel)
theorem q21_120:ThresholdAt 21 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 120 0 (by decide +kernel)
 · exact S 21 120 1 (by decide +kernel)
 · exact S 21 120 2 (by decide +kernel)
 · exact S 21 120 3 (by decide +kernel)
 · exact S 21 120 4 (by decide +kernel)
 · exact S 21 120 5 (by decide +kernel)
theorem q21_121:ThresholdAt 21 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 21 121 0 (by decide +kernel)
 · exact S 21 121 1 (by decide +kernel)
 · exact S 21 121 2 (by decide +kernel)
 · exact S 21 121 3 (by decide +kernel)
 · exact S 21 121 4 (by decide +kernel)
 · exact S 21 121 5 (by decide +kernel)
theorem checkedR21:∀ V ∈ List.range 122,ThresholdAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0_122:V < 61
  · by_cases h0_61:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q21_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q21_1
              · have he:V = 2:=by omega
                subst V
                exact q21_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q21_3
              · have he:V = 4:=by omega
                subst V
                exact q21_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q21_5
              · have he:V = 6:=by omega
                subst V
                exact q21_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q21_7
              · have he:V = 8:=by omega
                subst V
                exact q21_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q21_9
              · have he:V = 10:=by omega
                subst V
                exact q21_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q21_11
              · have he:V = 12:=by omega
                subst V
                exact q21_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q21_13
              · have he:V = 14:=by omega
                subst V
                exact q21_14
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have he:V = 15:=by omega
              subst V
              exact q21_15
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q21_16
              · have he:V = 17:=by omega
                subst V
                exact q21_17
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q21_18
              · have he:V = 19:=by omega
                subst V
                exact q21_19
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q21_20
              · have he:V = 21:=by omega
                subst V
                exact q21_21
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q21_22
              · have he:V = 23:=by omega
                subst V
                exact q21_23
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q21_24
              · have he:V = 25:=by omega
                subst V
                exact q21_25
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q21_26
              · have he:V = 27:=by omega
                subst V
                exact q21_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q21_28
              · have he:V = 29:=by omega
                subst V
                exact q21_29
    · by_cases h30_61:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have he:V = 30:=by omega
              subst V
              exact q21_30
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q21_31
              · have he:V = 32:=by omega
                subst V
                exact q21_32
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q21_33
              · have he:V = 34:=by omega
                subst V
                exact q21_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q21_35
              · have he:V = 36:=by omega
                subst V
                exact q21_36
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q21_37
              · have he:V = 38:=by omega
                subst V
                exact q21_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q21_39
              · have he:V = 40:=by omega
                subst V
                exact q21_40
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q21_41
              · have he:V = 42:=by omega
                subst V
                exact q21_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q21_43
              · have he:V = 44:=by omega
                subst V
                exact q21_44
      · by_cases h45_61:V < 53
        · by_cases h45_53:V < 49
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q21_45
              · have he:V = 46:=by omega
                subst V
                exact q21_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q21_47
              · have he:V = 48:=by omega
                subst V
                exact q21_48
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q21_49
              · have he:V = 50:=by omega
                subst V
                exact q21_50
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q21_51
              · have he:V = 52:=by omega
                subst V
                exact q21_52
        · by_cases h53_61:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q21_53
              · have he:V = 54:=by omega
                subst V
                exact q21_54
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q21_55
              · have he:V = 56:=by omega
                subst V
                exact q21_56
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q21_57
              · have he:V = 58:=by omega
                subst V
                exact q21_58
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q21_59
              · have he:V = 60:=by omega
                subst V
                exact q21_60
  · by_cases h61_122:V < 91
    · by_cases h61_91:V < 76
      · by_cases h61_76:V < 68
        · by_cases h61_68:V < 64
          · by_cases h61_64:V < 62
            · have he:V = 61:=by omega
              subst V
              exact q21_61
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q21_62
              · have he:V = 63:=by omega
                subst V
                exact q21_63
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q21_64
              · have he:V = 65:=by omega
                subst V
                exact q21_65
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q21_66
              · have he:V = 67:=by omega
                subst V
                exact q21_67
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q21_68
              · have he:V = 69:=by omega
                subst V
                exact q21_69
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q21_70
              · have he:V = 71:=by omega
                subst V
                exact q21_71
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q21_72
              · have he:V = 73:=by omega
                subst V
                exact q21_73
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q21_74
              · have he:V = 75:=by omega
                subst V
                exact q21_75
      · by_cases h76_91:V < 83
        · by_cases h76_83:V < 79
          · by_cases h76_79:V < 77
            · have he:V = 76:=by omega
              subst V
              exact q21_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q21_77
              · have he:V = 78:=by omega
                subst V
                exact q21_78
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q21_79
              · have he:V = 80:=by omega
                subst V
                exact q21_80
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q21_81
              · have he:V = 82:=by omega
                subst V
                exact q21_82
        · by_cases h83_91:V < 87
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q21_83
              · have he:V = 84:=by omega
                subst V
                exact q21_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q21_85
              · have he:V = 86:=by omega
                subst V
                exact q21_86
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q21_87
              · have he:V = 88:=by omega
                subst V
                exact q21_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q21_89
              · have he:V = 90:=by omega
                subst V
                exact q21_90
    · by_cases h91_122:V < 106
      · by_cases h91_106:V < 98
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have he:V = 91:=by omega
              subst V
              exact q21_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q21_92
              · have he:V = 93:=by omega
                subst V
                exact q21_93
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q21_94
              · have he:V = 95:=by omega
                subst V
                exact q21_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q21_96
              · have he:V = 97:=by omega
                subst V
                exact q21_97
        · by_cases h98_106:V < 102
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q21_98
              · have he:V = 99:=by omega
                subst V
                exact q21_99
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q21_100
              · have he:V = 101:=by omega
                subst V
                exact q21_101
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q21_102
              · have he:V = 103:=by omega
                subst V
                exact q21_103
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q21_104
              · have he:V = 105:=by omega
                subst V
                exact q21_105
      · by_cases h106_122:V < 114
        · by_cases h106_114:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q21_106
              · have he:V = 107:=by omega
                subst V
                exact q21_107
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q21_108
              · have he:V = 109:=by omega
                subst V
                exact q21_109
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q21_110
              · have he:V = 111:=by omega
                subst V
                exact q21_111
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q21_112
              · have he:V = 113:=by omega
                subst V
                exact q21_113
        · by_cases h114_122:V < 118
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q21_114
              · have he:V = 115:=by omega
                subst V
                exact q21_115
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q21_116
              · have he:V = 117:=by omega
                subst V
                exact q21_117
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q21_118
              · have he:V = 119:=by omega
                subst V
                exact q21_119
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q21_120
              · have he:V = 121:=by omega
                subst V
                exact q21_121
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
