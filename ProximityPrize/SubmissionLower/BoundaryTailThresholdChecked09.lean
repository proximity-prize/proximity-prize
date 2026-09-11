import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked08

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q9_0:ThresholdAt 9 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 0 0 (by decide +kernel)
 · exact S 9 0 1 (by decide +kernel)
 · exact S 9 0 2 (by decide +kernel)
 · exact S 9 0 3 (by decide +kernel)
 · exact S 9 0 4 (by decide +kernel)
 · exact S 9 0 5 (by decide +kernel)
theorem q9_1:ThresholdAt 9 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 1 0 (by decide +kernel)
 · exact S 9 1 1 (by decide +kernel)
 · exact S 9 1 2 (by decide +kernel)
 · exact S 9 1 3 (by decide +kernel)
 · exact S 9 1 4 (by decide +kernel)
 · exact S 9 1 5 (by decide +kernel)
theorem q9_2:ThresholdAt 9 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 2 0 (by decide +kernel)
 · exact S 9 2 1 (by decide +kernel)
 · exact S 9 2 2 (by decide +kernel)
 · exact S 9 2 3 (by decide +kernel)
 · exact S 9 2 4 (by decide +kernel)
 · exact S 9 2 5 (by decide +kernel)
theorem q9_3:ThresholdAt 9 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 3 0 (by decide +kernel)
 · exact S 9 3 1 (by decide +kernel)
 · exact S 9 3 2 (by decide +kernel)
 · exact S 9 3 3 (by decide +kernel)
 · exact S 9 3 4 (by decide +kernel)
 · exact S 9 3 5 (by decide +kernel)
theorem q9_4:ThresholdAt 9 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 4 0 (by decide +kernel)
 · exact S 9 4 1 (by decide +kernel)
 · exact S 9 4 2 (by decide +kernel)
 · exact S 9 4 3 (by decide +kernel)
 · exact S 9 4 4 (by decide +kernel)
 · exact S 9 4 5 (by decide +kernel)
theorem q9_5:ThresholdAt 9 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 5 0 (by decide +kernel)
 · exact S 9 5 1 (by decide +kernel)
 · exact S 9 5 2 (by decide +kernel)
 · exact S 9 5 3 (by decide +kernel)
 · exact S 9 5 4 (by decide +kernel)
 · exact S 9 5 5 (by decide +kernel)
theorem q9_6:ThresholdAt 9 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 6 0 (by decide +kernel)
 · exact S 9 6 1 (by decide +kernel)
 · exact S 9 6 2 (by decide +kernel)
 · exact S 9 6 3 (by decide +kernel)
 · exact S 9 6 4 (by decide +kernel)
 · exact S 9 6 5 (by decide +kernel)
theorem q9_7:ThresholdAt 9 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 7 0 (by decide +kernel)
 · exact S 9 7 1 (by decide +kernel)
 · exact S 9 7 2 (by decide +kernel)
 · exact S 9 7 3 (by decide +kernel)
 · exact S 9 7 4 (by decide +kernel)
 · exact S 9 7 5 (by decide +kernel)
theorem q9_8:ThresholdAt 9 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 8 0 (by decide +kernel)
 · exact S 9 8 1 (by decide +kernel)
 · exact S 9 8 2 (by decide +kernel)
 · exact S 9 8 3 (by decide +kernel)
 · exact S 9 8 4 (by decide +kernel)
 · exact S 9 8 5 (by decide +kernel)
theorem q9_9:ThresholdAt 9 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 9 0 (by decide +kernel)
 · exact S 9 9 1 (by decide +kernel)
 · exact S 9 9 2 (by decide +kernel)
 · exact S 9 9 3 (by decide +kernel)
 · exact S 9 9 4 (by decide +kernel)
 · exact S 9 9 5 (by decide +kernel)
theorem q9_10:ThresholdAt 9 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 10 0 (by decide +kernel)
 · exact S 9 10 1 (by decide +kernel)
 · exact S 9 10 2 (by decide +kernel)
 · exact S 9 10 3 (by decide +kernel)
 · exact S 9 10 4 (by decide +kernel)
 · exact S 9 10 5 (by decide +kernel)
theorem q9_11:ThresholdAt 9 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 11 0 (by decide +kernel)
 · exact S 9 11 1 (by decide +kernel)
 · exact S 9 11 2 (by decide +kernel)
 · exact S 9 11 3 (by decide +kernel)
 · exact S 9 11 4 (by decide +kernel)
 · exact S 9 11 5 (by decide +kernel)
theorem q9_12:ThresholdAt 9 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 12 0 (by decide +kernel)
 · exact S 9 12 1 (by decide +kernel)
 · exact S 9 12 2 (by decide +kernel)
 · exact S 9 12 3 (by decide +kernel)
 · exact S 9 12 4 (by decide +kernel)
 · exact S 9 12 5 (by decide +kernel)
theorem q9_13:ThresholdAt 9 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 13 0 (by decide +kernel)
 · exact S 9 13 1 (by decide +kernel)
 · exact S 9 13 2 (by decide +kernel)
 · exact S 9 13 3 (by decide +kernel)
 · exact S 9 13 4 (by decide +kernel)
 · exact S 9 13 5 (by decide +kernel)
theorem q9_14:ThresholdAt 9 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 14 0 (by decide +kernel)
 · exact S 9 14 1 (by decide +kernel)
 · exact S 9 14 2 (by decide +kernel)
 · exact S 9 14 3 (by decide +kernel)
 · exact S 9 14 4 (by decide +kernel)
 · exact S 9 14 5 (by decide +kernel)
theorem q9_15:ThresholdAt 9 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 15 0 (by decide +kernel)
 · exact S 9 15 1 (by decide +kernel)
 · exact S 9 15 2 (by decide +kernel)
 · exact S 9 15 3 (by decide +kernel)
 · exact S 9 15 4 (by decide +kernel)
 · exact S 9 15 5 (by decide +kernel)
theorem q9_16:ThresholdAt 9 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 16 0 (by decide +kernel)
 · exact S 9 16 1 (by decide +kernel)
 · exact S 9 16 2 (by decide +kernel)
 · exact S 9 16 3 (by decide +kernel)
 · exact S 9 16 4 (by decide +kernel)
 · exact S 9 16 5 (by decide +kernel)
theorem q9_17:ThresholdAt 9 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 17 0 (by decide +kernel)
 · exact S 9 17 1 (by decide +kernel)
 · exact S 9 17 2 (by decide +kernel)
 · exact S 9 17 3 (by decide +kernel)
 · exact S 9 17 4 (by decide +kernel)
 · exact S 9 17 5 (by decide +kernel)
theorem q9_18:ThresholdAt 9 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 18 0 (by decide +kernel)
 · exact S 9 18 1 (by decide +kernel)
 · exact S 9 18 2 (by decide +kernel)
 · exact S 9 18 3 (by decide +kernel)
 · exact S 9 18 4 (by decide +kernel)
 · exact S 9 18 5 (by decide +kernel)
theorem q9_19:ThresholdAt 9 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 19 0 (by decide +kernel)
 · exact S 9 19 1 (by decide +kernel)
 · exact S 9 19 2 (by decide +kernel)
 · exact S 9 19 3 (by decide +kernel)
 · exact S 9 19 4 (by decide +kernel)
 · exact S 9 19 5 (by decide +kernel)
theorem q9_20:ThresholdAt 9 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 20 0 (by decide +kernel)
 · exact S 9 20 1 (by decide +kernel)
 · exact S 9 20 2 (by decide +kernel)
 · exact S 9 20 3 (by decide +kernel)
 · exact S 9 20 4 (by decide +kernel)
 · exact S 9 20 5 (by decide +kernel)
theorem q9_21:ThresholdAt 9 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 21 0 (by decide +kernel)
 · exact S 9 21 1 (by decide +kernel)
 · exact S 9 21 2 (by decide +kernel)
 · exact S 9 21 3 (by decide +kernel)
 · exact S 9 21 4 (by decide +kernel)
 · exact S 9 21 5 (by decide +kernel)
theorem q9_22:ThresholdAt 9 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 22 0 (by decide +kernel)
 · exact S 9 22 1 (by decide +kernel)
 · exact S 9 22 2 (by decide +kernel)
 · exact S 9 22 3 (by decide +kernel)
 · exact S 9 22 4 (by decide +kernel)
 · exact S 9 22 5 (by decide +kernel)
theorem q9_23:ThresholdAt 9 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 23 0 (by decide +kernel)
 · exact S 9 23 1 (by decide +kernel)
 · exact S 9 23 2 (by decide +kernel)
 · exact S 9 23 3 (by decide +kernel)
 · exact S 9 23 4 (by decide +kernel)
 · exact S 9 23 5 (by decide +kernel)
theorem q9_24:ThresholdAt 9 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 24 0 (by decide +kernel)
 · exact S 9 24 1 (by decide +kernel)
 · exact S 9 24 2 (by decide +kernel)
 · exact S 9 24 3 (by decide +kernel)
 · exact S 9 24 4 (by decide +kernel)
 · exact S 9 24 5 (by decide +kernel)
theorem q9_25:ThresholdAt 9 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 25 0 (by decide +kernel)
 · exact S 9 25 1 (by decide +kernel)
 · exact S 9 25 2 (by decide +kernel)
 · exact S 9 25 3 (by decide +kernel)
 · exact S 9 25 4 (by decide +kernel)
 · exact S 9 25 5 (by decide +kernel)
theorem q9_26:ThresholdAt 9 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 26 0 (by decide +kernel)
 · exact S 9 26 1 (by decide +kernel)
 · exact S 9 26 2 (by decide +kernel)
 · exact S 9 26 3 (by decide +kernel)
 · exact S 9 26 4 (by decide +kernel)
 · exact S 9 26 5 (by decide +kernel)
theorem q9_27:ThresholdAt 9 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 27 0 (by decide +kernel)
 · exact S 9 27 1 (by decide +kernel)
 · exact S 9 27 2 (by decide +kernel)
 · exact S 9 27 3 (by decide +kernel)
 · exact S 9 27 4 (by decide +kernel)
 · exact S 9 27 5 (by decide +kernel)
theorem q9_28:ThresholdAt 9 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 28 0 (by decide +kernel)
 · exact S 9 28 1 (by decide +kernel)
 · exact S 9 28 2 (by decide +kernel)
 · exact S 9 28 3 (by decide +kernel)
 · exact S 9 28 4 (by decide +kernel)
 · exact S 9 28 5 (by decide +kernel)
theorem q9_29:ThresholdAt 9 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 29 0 (by decide +kernel)
 · exact S 9 29 1 (by decide +kernel)
 · exact S 9 29 2 (by decide +kernel)
 · exact S 9 29 3 (by decide +kernel)
 · exact S 9 29 4 (by decide +kernel)
 · exact S 9 29 5 (by decide +kernel)
theorem q9_30:ThresholdAt 9 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 30 0 (by decide +kernel)
 · exact S 9 30 1 (by decide +kernel)
 · exact S 9 30 2 (by decide +kernel)
 · exact S 9 30 3 (by decide +kernel)
 · exact S 9 30 4 (by decide +kernel)
 · exact S 9 30 5 (by decide +kernel)
theorem q9_31:ThresholdAt 9 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 31 0 (by decide +kernel)
 · exact S 9 31 1 (by decide +kernel)
 · exact S 9 31 2 (by decide +kernel)
 · exact S 9 31 3 (by decide +kernel)
 · exact S 9 31 4 (by decide +kernel)
 · exact S 9 31 5 (by decide +kernel)
theorem q9_32:ThresholdAt 9 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 32 0 (by decide +kernel)
 · exact S 9 32 1 (by decide +kernel)
 · exact S 9 32 2 (by decide +kernel)
 · exact S 9 32 3 (by decide +kernel)
 · exact S 9 32 4 (by decide +kernel)
 · exact S 9 32 5 (by decide +kernel)
theorem q9_33:ThresholdAt 9 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 33 0 (by decide +kernel)
 · exact S 9 33 1 (by decide +kernel)
 · exact S 9 33 2 (by decide +kernel)
 · exact S 9 33 3 (by decide +kernel)
 · exact S 9 33 4 (by decide +kernel)
 · exact S 9 33 5 (by decide +kernel)
theorem q9_34:ThresholdAt 9 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 34 0 (by decide +kernel)
 · exact S 9 34 1 (by decide +kernel)
 · exact S 9 34 2 (by decide +kernel)
 · exact S 9 34 3 (by decide +kernel)
 · exact S 9 34 4 (by decide +kernel)
 · exact S 9 34 5 (by decide +kernel)
theorem q9_35:ThresholdAt 9 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 35 0 (by decide +kernel)
 · exact S 9 35 1 (by decide +kernel)
 · exact S 9 35 2 (by decide +kernel)
 · exact S 9 35 3 (by decide +kernel)
 · exact S 9 35 4 (by decide +kernel)
 · exact S 9 35 5 (by decide +kernel)
theorem q9_36:ThresholdAt 9 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 36 0 (by decide +kernel)
 · exact S 9 36 1 (by decide +kernel)
 · exact S 9 36 2 (by decide +kernel)
 · exact S 9 36 3 (by decide +kernel)
 · exact S 9 36 4 (by decide +kernel)
 · exact S 9 36 5 (by decide +kernel)
theorem q9_37:ThresholdAt 9 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 37 0 (by decide +kernel)
 · exact S 9 37 1 (by decide +kernel)
 · exact S 9 37 2 (by decide +kernel)
 · exact S 9 37 3 (by decide +kernel)
 · exact S 9 37 4 (by decide +kernel)
 · exact S 9 37 5 (by decide +kernel)
theorem q9_38:ThresholdAt 9 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 38 0 (by decide +kernel)
 · exact S 9 38 1 (by decide +kernel)
 · exact S 9 38 2 (by decide +kernel)
 · exact S 9 38 3 (by decide +kernel)
 · exact S 9 38 4 (by decide +kernel)
 · exact S 9 38 5 (by decide +kernel)
theorem q9_39:ThresholdAt 9 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 39 0 (by decide +kernel)
 · exact S 9 39 1 (by decide +kernel)
 · exact S 9 39 2 (by decide +kernel)
 · exact S 9 39 3 (by decide +kernel)
 · exact S 9 39 4 (by decide +kernel)
 · exact S 9 39 5 (by decide +kernel)
theorem q9_40:ThresholdAt 9 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 40 0 (by decide +kernel)
 · exact S 9 40 1 (by decide +kernel)
 · exact S 9 40 2 (by decide +kernel)
 · exact S 9 40 3 (by decide +kernel)
 · exact S 9 40 4 (by decide +kernel)
 · exact S 9 40 5 (by decide +kernel)
theorem q9_41:ThresholdAt 9 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 41 0 (by decide +kernel)
 · exact S 9 41 1 (by decide +kernel)
 · exact S 9 41 2 (by decide +kernel)
 · exact S 9 41 3 (by decide +kernel)
 · exact S 9 41 4 (by decide +kernel)
 · exact S 9 41 5 (by decide +kernel)
theorem q9_42:ThresholdAt 9 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 42 0 (by decide +kernel)
 · exact S 9 42 1 (by decide +kernel)
 · exact S 9 42 2 (by decide +kernel)
 · exact S 9 42 3 (by decide +kernel)
 · exact S 9 42 4 (by decide +kernel)
 · exact S 9 42 5 (by decide +kernel)
theorem q9_43:ThresholdAt 9 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 43 0 (by decide +kernel)
 · exact S 9 43 1 (by decide +kernel)
 · exact S 9 43 2 (by decide +kernel)
 · exact S 9 43 3 (by decide +kernel)
 · exact S 9 43 4 (by decide +kernel)
 · exact S 9 43 5 (by decide +kernel)
theorem q9_44:ThresholdAt 9 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 44 0 (by decide +kernel)
 · exact S 9 44 1 (by decide +kernel)
 · exact S 9 44 2 (by decide +kernel)
 · exact S 9 44 3 (by decide +kernel)
 · exact S 9 44 4 (by decide +kernel)
 · exact S 9 44 5 (by decide +kernel)
theorem q9_45:ThresholdAt 9 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 45 0 (by decide +kernel)
 · exact S 9 45 1 (by decide +kernel)
 · exact S 9 45 2 (by decide +kernel)
 · exact S 9 45 3 (by decide +kernel)
 · exact S 9 45 4 (by decide +kernel)
 · exact S 9 45 5 (by decide +kernel)
theorem q9_46:ThresholdAt 9 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 46 0 (by decide +kernel)
 · exact S 9 46 1 (by decide +kernel)
 · exact S 9 46 2 (by decide +kernel)
 · exact S 9 46 3 (by decide +kernel)
 · exact S 9 46 4 (by decide +kernel)
 · exact S 9 46 5 (by decide +kernel)
theorem q9_47:ThresholdAt 9 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 47 0 (by decide +kernel)
 · exact S 9 47 1 (by decide +kernel)
 · exact S 9 47 2 (by decide +kernel)
 · exact S 9 47 3 (by decide +kernel)
 · exact S 9 47 4 (by decide +kernel)
 · exact S 9 47 5 (by decide +kernel)
theorem q9_48:ThresholdAt 9 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 48 0 (by decide +kernel)
 · exact S 9 48 1 (by decide +kernel)
 · exact S 9 48 2 (by decide +kernel)
 · exact S 9 48 3 (by decide +kernel)
 · exact S 9 48 4 (by decide +kernel)
 · exact S 9 48 5 (by decide +kernel)
theorem q9_49:ThresholdAt 9 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 49 0 (by decide +kernel)
 · exact S 9 49 1 (by decide +kernel)
 · exact S 9 49 2 (by decide +kernel)
 · exact S 9 49 3 (by decide +kernel)
 · exact S 9 49 4 (by decide +kernel)
 · exact S 9 49 5 (by decide +kernel)
theorem q9_50:ThresholdAt 9 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 50 0 (by decide +kernel)
 · exact S 9 50 1 (by decide +kernel)
 · exact S 9 50 2 (by decide +kernel)
 · exact S 9 50 3 (by decide +kernel)
 · exact S 9 50 4 (by decide +kernel)
 · exact S 9 50 5 (by decide +kernel)
theorem q9_51:ThresholdAt 9 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 51 0 (by decide +kernel)
 · exact S 9 51 1 (by decide +kernel)
 · exact S 9 51 2 (by decide +kernel)
 · exact S 9 51 3 (by decide +kernel)
 · exact S 9 51 4 (by decide +kernel)
 · exact S 9 51 5 (by decide +kernel)
theorem q9_52:ThresholdAt 9 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 52 0 (by decide +kernel)
 · exact S 9 52 1 (by decide +kernel)
 · exact S 9 52 2 (by decide +kernel)
 · exact S 9 52 3 (by decide +kernel)
 · exact S 9 52 4 (by decide +kernel)
 · exact S 9 52 5 (by decide +kernel)
theorem q9_53:ThresholdAt 9 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 53 0 (by decide +kernel)
 · exact S 9 53 1 (by decide +kernel)
 · exact S 9 53 2 (by decide +kernel)
 · exact S 9 53 3 (by decide +kernel)
 · exact S 9 53 4 (by decide +kernel)
 · exact S 9 53 5 (by decide +kernel)
theorem q9_54:ThresholdAt 9 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 54 0 (by decide +kernel)
 · exact S 9 54 1 (by decide +kernel)
 · exact S 9 54 2 (by decide +kernel)
 · exact S 9 54 3 (by decide +kernel)
 · exact S 9 54 4 (by decide +kernel)
 · exact S 9 54 5 (by decide +kernel)
theorem q9_55:ThresholdAt 9 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 55 0 (by decide +kernel)
 · exact S 9 55 1 (by decide +kernel)
 · exact S 9 55 2 (by decide +kernel)
 · exact S 9 55 3 (by decide +kernel)
 · exact S 9 55 4 (by decide +kernel)
 · exact S 9 55 5 (by decide +kernel)
theorem q9_56:ThresholdAt 9 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 56 0 (by decide +kernel)
 · exact S 9 56 1 (by decide +kernel)
 · exact S 9 56 2 (by decide +kernel)
 · exact S 9 56 3 (by decide +kernel)
 · exact S 9 56 4 (by decide +kernel)
 · exact S 9 56 5 (by decide +kernel)
theorem q9_57:ThresholdAt 9 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 57 0 (by decide +kernel)
 · exact S 9 57 1 (by decide +kernel)
 · exact S 9 57 2 (by decide +kernel)
 · exact S 9 57 3 (by decide +kernel)
 · exact S 9 57 4 (by decide +kernel)
 · exact S 9 57 5 (by decide +kernel)
theorem q9_58:ThresholdAt 9 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 58 0 (by decide +kernel)
 · exact S 9 58 1 (by decide +kernel)
 · exact S 9 58 2 (by decide +kernel)
 · exact S 9 58 3 (by decide +kernel)
 · exact S 9 58 4 (by decide +kernel)
 · exact S 9 58 5 (by decide +kernel)
theorem q9_59:ThresholdAt 9 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 59 0 (by decide +kernel)
 · exact S 9 59 1 (by decide +kernel)
 · exact S 9 59 2 (by decide +kernel)
 · exact S 9 59 3 (by decide +kernel)
 · exact S 9 59 4 (by decide +kernel)
 · exact S 9 59 5 (by decide +kernel)
theorem q9_60:ThresholdAt 9 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 60 0 (by decide +kernel)
 · exact S 9 60 1 (by decide +kernel)
 · exact S 9 60 2 (by decide +kernel)
 · exact S 9 60 3 (by decide +kernel)
 · exact S 9 60 4 (by decide +kernel)
 · exact S 9 60 5 (by decide +kernel)
theorem q9_61:ThresholdAt 9 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 61 0 (by decide +kernel)
 · exact S 9 61 1 (by decide +kernel)
 · exact S 9 61 2 (by decide +kernel)
 · exact S 9 61 3 (by decide +kernel)
 · exact S 9 61 4 (by decide +kernel)
 · exact S 9 61 5 (by decide +kernel)
theorem q9_62:ThresholdAt 9 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 62 0 (by decide +kernel)
 · exact S 9 62 1 (by decide +kernel)
 · exact S 9 62 2 (by decide +kernel)
 · exact S 9 62 3 (by decide +kernel)
 · exact S 9 62 4 (by decide +kernel)
 · exact S 9 62 5 (by decide +kernel)
theorem q9_63:ThresholdAt 9 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 63 0 (by decide +kernel)
 · exact S 9 63 1 (by decide +kernel)
 · exact S 9 63 2 (by decide +kernel)
 · exact S 9 63 3 (by decide +kernel)
 · exact S 9 63 4 (by decide +kernel)
 · exact S 9 63 5 (by decide +kernel)
theorem q9_64:ThresholdAt 9 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 64 0 (by decide +kernel)
 · exact S 9 64 1 (by decide +kernel)
 · exact S 9 64 2 (by decide +kernel)
 · exact S 9 64 3 (by decide +kernel)
 · exact S 9 64 4 (by decide +kernel)
 · exact S 9 64 5 (by decide +kernel)
theorem q9_65:ThresholdAt 9 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 65 0 (by decide +kernel)
 · exact S 9 65 1 (by decide +kernel)
 · exact S 9 65 2 (by decide +kernel)
 · exact S 9 65 3 (by decide +kernel)
 · exact S 9 65 4 (by decide +kernel)
 · exact S 9 65 5 (by decide +kernel)
theorem q9_66:ThresholdAt 9 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 66 0 (by decide +kernel)
 · exact S 9 66 1 (by decide +kernel)
 · exact S 9 66 2 (by decide +kernel)
 · exact S 9 66 3 (by decide +kernel)
 · exact S 9 66 4 (by decide +kernel)
 · exact S 9 66 5 (by decide +kernel)
theorem q9_67:ThresholdAt 9 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 67 0 (by decide +kernel)
 · exact S 9 67 1 (by decide +kernel)
 · exact S 9 67 2 (by decide +kernel)
 · exact S 9 67 3 (by decide +kernel)
 · exact S 9 67 4 (by decide +kernel)
 · exact S 9 67 5 (by decide +kernel)
theorem q9_68:ThresholdAt 9 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 68 0 (by decide +kernel)
 · exact S 9 68 1 (by decide +kernel)
 · exact S 9 68 2 (by decide +kernel)
 · exact S 9 68 3 (by decide +kernel)
 · exact S 9 68 4 (by decide +kernel)
 · exact S 9 68 5 (by decide +kernel)
theorem q9_69:ThresholdAt 9 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 69 0 (by decide +kernel)
 · exact S 9 69 1 (by decide +kernel)
 · exact S 9 69 2 (by decide +kernel)
 · exact S 9 69 3 (by decide +kernel)
 · exact S 9 69 4 (by decide +kernel)
 · exact S 9 69 5 (by decide +kernel)
theorem q9_70:ThresholdAt 9 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 70 0 (by decide +kernel)
 · exact S 9 70 1 (by decide +kernel)
 · exact S 9 70 2 (by decide +kernel)
 · exact S 9 70 3 (by decide +kernel)
 · exact S 9 70 4 (by decide +kernel)
 · exact S 9 70 5 (by decide +kernel)
theorem q9_71:ThresholdAt 9 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 71 0 (by decide +kernel)
 · exact S 9 71 1 (by decide +kernel)
 · exact S 9 71 2 (by decide +kernel)
 · exact S 9 71 3 (by decide +kernel)
 · exact S 9 71 4 (by decide +kernel)
 · exact S 9 71 5 (by decide +kernel)
theorem q9_72:ThresholdAt 9 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 72 0 (by decide +kernel)
 · exact S 9 72 1 (by decide +kernel)
 · exact S 9 72 2 (by decide +kernel)
 · exact S 9 72 3 (by decide +kernel)
 · exact S 9 72 4 (by decide +kernel)
 · exact S 9 72 5 (by decide +kernel)
theorem q9_73:ThresholdAt 9 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 73 0 (by decide +kernel)
 · exact S 9 73 1 (by decide +kernel)
 · exact S 9 73 2 (by decide +kernel)
 · exact S 9 73 3 (by decide +kernel)
 · exact S 9 73 4 (by decide +kernel)
 · exact S 9 73 5 (by decide +kernel)
theorem q9_74:ThresholdAt 9 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 74 0 (by decide +kernel)
 · exact S 9 74 1 (by decide +kernel)
 · exact S 9 74 2 (by decide +kernel)
 · exact S 9 74 3 (by decide +kernel)
 · exact S 9 74 4 (by decide +kernel)
 · exact S 9 74 5 (by decide +kernel)
theorem q9_75:ThresholdAt 9 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 75 0 (by decide +kernel)
 · exact S 9 75 1 (by decide +kernel)
 · exact S 9 75 2 (by decide +kernel)
 · exact S 9 75 3 (by decide +kernel)
 · exact S 9 75 4 (by decide +kernel)
 · exact S 9 75 5 (by decide +kernel)
theorem q9_76:ThresholdAt 9 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 76 0 (by decide +kernel)
 · exact S 9 76 1 (by decide +kernel)
 · exact S 9 76 2 (by decide +kernel)
 · exact S 9 76 3 (by decide +kernel)
 · exact S 9 76 4 (by decide +kernel)
 · exact S 9 76 5 (by decide +kernel)
theorem q9_77:ThresholdAt 9 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 77 0 (by decide +kernel)
 · exact S 9 77 1 (by decide +kernel)
 · exact S 9 77 2 (by decide +kernel)
 · exact S 9 77 3 (by decide +kernel)
 · exact S 9 77 4 (by decide +kernel)
 · exact S 9 77 5 (by decide +kernel)
theorem q9_78:ThresholdAt 9 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 78 0 (by decide +kernel)
 · exact S 9 78 1 (by decide +kernel)
 · exact S 9 78 2 (by decide +kernel)
 · exact S 9 78 3 (by decide +kernel)
 · exact S 9 78 4 (by decide +kernel)
 · exact S 9 78 5 (by decide +kernel)
theorem q9_79:ThresholdAt 9 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 79 0 (by decide +kernel)
 · exact S 9 79 1 (by decide +kernel)
 · exact S 9 79 2 (by decide +kernel)
 · exact S 9 79 3 (by decide +kernel)
 · exact S 9 79 4 (by decide +kernel)
 · exact S 9 79 5 (by decide +kernel)
theorem q9_80:ThresholdAt 9 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 80 0 (by decide +kernel)
 · exact S 9 80 1 (by decide +kernel)
 · exact S 9 80 2 (by decide +kernel)
 · exact S 9 80 3 (by decide +kernel)
 · exact S 9 80 4 (by decide +kernel)
 · exact S 9 80 5 (by decide +kernel)
theorem q9_81:ThresholdAt 9 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 81 0 (by decide +kernel)
 · exact S 9 81 1 (by decide +kernel)
 · exact S 9 81 2 (by decide +kernel)
 · exact S 9 81 3 (by decide +kernel)
 · exact S 9 81 4 (by decide +kernel)
 · exact S 9 81 5 (by decide +kernel)
theorem q9_82:ThresholdAt 9 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 82 0 (by decide +kernel)
 · exact S 9 82 1 (by decide +kernel)
 · exact S 9 82 2 (by decide +kernel)
 · exact S 9 82 3 (by decide +kernel)
 · exact S 9 82 4 (by decide +kernel)
 · exact S 9 82 5 (by decide +kernel)
theorem q9_83:ThresholdAt 9 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 83 0 (by decide +kernel)
 · exact S 9 83 1 (by decide +kernel)
 · exact S 9 83 2 (by decide +kernel)
 · exact S 9 83 3 (by decide +kernel)
 · exact S 9 83 4 (by decide +kernel)
 · exact S 9 83 5 (by decide +kernel)
theorem q9_84:ThresholdAt 9 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 84 0 (by decide +kernel)
 · exact S 9 84 1 (by decide +kernel)
 · exact S 9 84 2 (by decide +kernel)
 · exact S 9 84 3 (by decide +kernel)
 · exact S 9 84 4 (by decide +kernel)
 · exact S 9 84 5 (by decide +kernel)
theorem q9_85:ThresholdAt 9 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 85 0 (by decide +kernel)
 · exact S 9 85 1 (by decide +kernel)
 · exact S 9 85 2 (by decide +kernel)
 · exact S 9 85 3 (by decide +kernel)
 · exact S 9 85 4 (by decide +kernel)
 · exact S 9 85 5 (by decide +kernel)
theorem q9_86:ThresholdAt 9 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 86 0 (by decide +kernel)
 · exact S 9 86 1 (by decide +kernel)
 · exact S 9 86 2 (by decide +kernel)
 · exact S 9 86 3 (by decide +kernel)
 · exact S 9 86 4 (by decide +kernel)
 · exact S 9 86 5 (by decide +kernel)
theorem q9_87:ThresholdAt 9 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 87 0 (by decide +kernel)
 · exact S 9 87 1 (by decide +kernel)
 · exact S 9 87 2 (by decide +kernel)
 · exact S 9 87 3 (by decide +kernel)
 · exact S 9 87 4 (by decide +kernel)
 · exact S 9 87 5 (by decide +kernel)
theorem q9_88:ThresholdAt 9 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 88 0 (by decide +kernel)
 · exact S 9 88 1 (by decide +kernel)
 · exact S 9 88 2 (by decide +kernel)
 · exact S 9 88 3 (by decide +kernel)
 · exact S 9 88 4 (by decide +kernel)
 · exact S 9 88 5 (by decide +kernel)
theorem q9_89:ThresholdAt 9 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 89 0 (by decide +kernel)
 · exact S 9 89 1 (by decide +kernel)
 · exact S 9 89 2 (by decide +kernel)
 · exact S 9 89 3 (by decide +kernel)
 · exact S 9 89 4 (by decide +kernel)
 · exact S 9 89 5 (by decide +kernel)
theorem q9_90:ThresholdAt 9 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 90 0 (by decide +kernel)
 · exact S 9 90 1 (by decide +kernel)
 · exact S 9 90 2 (by decide +kernel)
 · exact S 9 90 3 (by decide +kernel)
 · exact S 9 90 4 (by decide +kernel)
 · exact S 9 90 5 (by decide +kernel)
theorem q9_91:ThresholdAt 9 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 91 0 (by decide +kernel)
 · exact S 9 91 1 (by decide +kernel)
 · exact S 9 91 2 (by decide +kernel)
 · exact S 9 91 3 (by decide +kernel)
 · exact S 9 91 4 (by decide +kernel)
 · exact S 9 91 5 (by decide +kernel)
theorem q9_92:ThresholdAt 9 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 92 0 (by decide +kernel)
 · exact S 9 92 1 (by decide +kernel)
 · exact S 9 92 2 (by decide +kernel)
 · exact S 9 92 3 (by decide +kernel)
 · exact S 9 92 4 (by decide +kernel)
 · exact S 9 92 5 (by decide +kernel)
theorem q9_93:ThresholdAt 9 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 93 0 (by decide +kernel)
 · exact S 9 93 1 (by decide +kernel)
 · exact S 9 93 2 (by decide +kernel)
 · exact S 9 93 3 (by decide +kernel)
 · exact S 9 93 4 (by decide +kernel)
 · exact S 9 93 5 (by decide +kernel)
theorem q9_94:ThresholdAt 9 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 94 0 (by decide +kernel)
 · exact S 9 94 1 (by decide +kernel)
 · exact S 9 94 2 (by decide +kernel)
 · exact S 9 94 3 (by decide +kernel)
 · exact S 9 94 4 (by decide +kernel)
 · exact S 9 94 5 (by decide +kernel)
theorem q9_95:ThresholdAt 9 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 95 0 (by decide +kernel)
 · exact S 9 95 1 (by decide +kernel)
 · exact S 9 95 2 (by decide +kernel)
 · exact S 9 95 3 (by decide +kernel)
 · exact S 9 95 4 (by decide +kernel)
 · exact S 9 95 5 (by decide +kernel)
theorem q9_96:ThresholdAt 9 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 96 0 (by decide +kernel)
 · exact S 9 96 1 (by decide +kernel)
 · exact S 9 96 2 (by decide +kernel)
 · exact S 9 96 3 (by decide +kernel)
 · exact S 9 96 4 (by decide +kernel)
 · exact S 9 96 5 (by decide +kernel)
theorem q9_97:ThresholdAt 9 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 97 0 (by decide +kernel)
 · exact S 9 97 1 (by decide +kernel)
 · exact S 9 97 2 (by decide +kernel)
 · exact S 9 97 3 (by decide +kernel)
 · exact S 9 97 4 (by decide +kernel)
 · exact S 9 97 5 (by decide +kernel)
theorem q9_98:ThresholdAt 9 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 98 0 (by decide +kernel)
 · exact S 9 98 1 (by decide +kernel)
 · exact S 9 98 2 (by decide +kernel)
 · exact S 9 98 3 (by decide +kernel)
 · exact S 9 98 4 (by decide +kernel)
 · exact S 9 98 5 (by decide +kernel)
theorem q9_99:ThresholdAt 9 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 99 0 (by decide +kernel)
 · exact S 9 99 1 (by decide +kernel)
 · exact S 9 99 2 (by decide +kernel)
 · exact S 9 99 3 (by decide +kernel)
 · exact S 9 99 4 (by decide +kernel)
 · exact S 9 99 5 (by decide +kernel)
theorem q9_100:ThresholdAt 9 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 100 0 (by decide +kernel)
 · exact S 9 100 1 (by decide +kernel)
 · exact S 9 100 2 (by decide +kernel)
 · exact S 9 100 3 (by decide +kernel)
 · exact S 9 100 4 (by decide +kernel)
 · exact S 9 100 5 (by decide +kernel)
theorem q9_101:ThresholdAt 9 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 101 0 (by decide +kernel)
 · exact S 9 101 1 (by decide +kernel)
 · exact S 9 101 2 (by decide +kernel)
 · exact S 9 101 3 (by decide +kernel)
 · exact S 9 101 4 (by decide +kernel)
 · exact S 9 101 5 (by decide +kernel)
theorem q9_102:ThresholdAt 9 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 102 0 (by decide +kernel)
 · exact S 9 102 1 (by decide +kernel)
 · exact S 9 102 2 (by decide +kernel)
 · exact S 9 102 3 (by decide +kernel)
 · exact S 9 102 4 (by decide +kernel)
 · exact S 9 102 5 (by decide +kernel)
theorem q9_103:ThresholdAt 9 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 103 0 (by decide +kernel)
 · exact S 9 103 1 (by decide +kernel)
 · exact S 9 103 2 (by decide +kernel)
 · exact S 9 103 3 (by decide +kernel)
 · exact S 9 103 4 (by decide +kernel)
 · exact S 9 103 5 (by decide +kernel)
theorem q9_104:ThresholdAt 9 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 104 0 (by decide +kernel)
 · exact S 9 104 1 (by decide +kernel)
 · exact S 9 104 2 (by decide +kernel)
 · exact S 9 104 3 (by decide +kernel)
 · exact S 9 104 4 (by decide +kernel)
 · exact S 9 104 5 (by decide +kernel)
theorem q9_105:ThresholdAt 9 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 105 0 (by decide +kernel)
 · exact S 9 105 1 (by decide +kernel)
 · exact S 9 105 2 (by decide +kernel)
 · exact S 9 105 3 (by decide +kernel)
 · exact S 9 105 4 (by decide +kernel)
 · exact S 9 105 5 (by decide +kernel)
theorem q9_106:ThresholdAt 9 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 106 0 (by decide +kernel)
 · exact S 9 106 1 (by decide +kernel)
 · exact S 9 106 2 (by decide +kernel)
 · exact S 9 106 3 (by decide +kernel)
 · exact S 9 106 4 (by decide +kernel)
 · exact S 9 106 5 (by decide +kernel)
theorem q9_107:ThresholdAt 9 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 107 0 (by decide +kernel)
 · exact S 9 107 1 (by decide +kernel)
 · exact S 9 107 2 (by decide +kernel)
 · exact S 9 107 3 (by decide +kernel)
 · exact S 9 107 4 (by decide +kernel)
 · exact S 9 107 5 (by decide +kernel)
theorem q9_108:ThresholdAt 9 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 108 0 (by decide +kernel)
 · exact S 9 108 1 (by decide +kernel)
 · exact S 9 108 2 (by decide +kernel)
 · exact S 9 108 3 (by decide +kernel)
 · exact S 9 108 4 (by decide +kernel)
 · exact S 9 108 5 (by decide +kernel)
theorem q9_109:ThresholdAt 9 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 109 0 (by decide +kernel)
 · exact S 9 109 1 (by decide +kernel)
 · exact S 9 109 2 (by decide +kernel)
 · exact S 9 109 3 (by decide +kernel)
 · exact S 9 109 4 (by decide +kernel)
 · exact S 9 109 5 (by decide +kernel)
theorem q9_110:ThresholdAt 9 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 110 0 (by decide +kernel)
 · exact S 9 110 1 (by decide +kernel)
 · exact S 9 110 2 (by decide +kernel)
 · exact S 9 110 3 (by decide +kernel)
 · exact S 9 110 4 (by decide +kernel)
 · exact S 9 110 5 (by decide +kernel)
theorem q9_111:ThresholdAt 9 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 111 0 (by decide +kernel)
 · exact S 9 111 1 (by decide +kernel)
 · exact S 9 111 2 (by decide +kernel)
 · exact S 9 111 3 (by decide +kernel)
 · exact S 9 111 4 (by decide +kernel)
 · exact S 9 111 5 (by decide +kernel)
theorem q9_112:ThresholdAt 9 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 112 0 (by decide +kernel)
 · exact S 9 112 1 (by decide +kernel)
 · exact S 9 112 2 (by decide +kernel)
 · exact S 9 112 3 (by decide +kernel)
 · exact S 9 112 4 (by decide +kernel)
 · exact S 9 112 5 (by decide +kernel)
theorem q9_113:ThresholdAt 9 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 113 0 (by decide +kernel)
 · exact S 9 113 1 (by decide +kernel)
 · exact S 9 113 2 (by decide +kernel)
 · exact S 9 113 3 (by decide +kernel)
 · exact S 9 113 4 (by decide +kernel)
 · exact S 9 113 5 (by decide +kernel)
theorem q9_114:ThresholdAt 9 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 114 0 (by decide +kernel)
 · exact S 9 114 1 (by decide +kernel)
 · exact S 9 114 2 (by decide +kernel)
 · exact S 9 114 3 (by decide +kernel)
 · exact S 9 114 4 (by decide +kernel)
 · exact S 9 114 5 (by decide +kernel)
theorem q9_115:ThresholdAt 9 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 115 0 (by decide +kernel)
 · exact S 9 115 1 (by decide +kernel)
 · exact S 9 115 2 (by decide +kernel)
 · exact S 9 115 3 (by decide +kernel)
 · exact S 9 115 4 (by decide +kernel)
 · exact S 9 115 5 (by decide +kernel)
theorem q9_116:ThresholdAt 9 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 116 0 (by decide +kernel)
 · exact S 9 116 1 (by decide +kernel)
 · exact S 9 116 2 (by decide +kernel)
 · exact S 9 116 3 (by decide +kernel)
 · exact S 9 116 4 (by decide +kernel)
 · exact S 9 116 5 (by decide +kernel)
theorem q9_117:ThresholdAt 9 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 117 0 (by decide +kernel)
 · exact S 9 117 1 (by decide +kernel)
 · exact S 9 117 2 (by decide +kernel)
 · exact S 9 117 3 (by decide +kernel)
 · exact S 9 117 4 (by decide +kernel)
 · exact S 9 117 5 (by decide +kernel)
theorem q9_118:ThresholdAt 9 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 118 0 (by decide +kernel)
 · exact S 9 118 1 (by decide +kernel)
 · exact S 9 118 2 (by decide +kernel)
 · exact S 9 118 3 (by decide +kernel)
 · exact S 9 118 4 (by decide +kernel)
 · exact S 9 118 5 (by decide +kernel)
theorem q9_119:ThresholdAt 9 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 119 0 (by decide +kernel)
 · exact S 9 119 1 (by decide +kernel)
 · exact S 9 119 2 (by decide +kernel)
 · exact S 9 119 3 (by decide +kernel)
 · exact S 9 119 4 (by decide +kernel)
 · exact S 9 119 5 (by decide +kernel)
theorem q9_120:ThresholdAt 9 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 120 0 (by decide +kernel)
 · exact S 9 120 1 (by decide +kernel)
 · exact S 9 120 2 (by decide +kernel)
 · exact S 9 120 3 (by decide +kernel)
 · exact S 9 120 4 (by decide +kernel)
 · exact S 9 120 5 (by decide +kernel)
theorem q9_121:ThresholdAt 9 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 121 0 (by decide +kernel)
 · exact S 9 121 1 (by decide +kernel)
 · exact S 9 121 2 (by decide +kernel)
 · exact S 9 121 3 (by decide +kernel)
 · exact S 9 121 4 (by decide +kernel)
 · exact S 9 121 5 (by decide +kernel)
theorem q9_122:ThresholdAt 9 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 122 0 (by decide +kernel)
 · exact S 9 122 1 (by decide +kernel)
 · exact S 9 122 2 (by decide +kernel)
 · exact S 9 122 3 (by decide +kernel)
 · exact S 9 122 4 (by decide +kernel)
 · exact S 9 122 5 (by decide +kernel)
theorem q9_123:ThresholdAt 9 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 123 0 (by decide +kernel)
 · exact S 9 123 1 (by decide +kernel)
 · exact S 9 123 2 (by decide +kernel)
 · exact S 9 123 3 (by decide +kernel)
 · exact S 9 123 4 (by decide +kernel)
 · exact S 9 123 5 (by decide +kernel)
theorem q9_124:ThresholdAt 9 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 124 0 (by decide +kernel)
 · exact S 9 124 1 (by decide +kernel)
 · exact S 9 124 2 (by decide +kernel)
 · exact S 9 124 3 (by decide +kernel)
 · exact S 9 124 4 (by decide +kernel)
 · exact S 9 124 5 (by decide +kernel)
theorem q9_125:ThresholdAt 9 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 125 0 (by decide +kernel)
 · exact S 9 125 1 (by decide +kernel)
 · exact S 9 125 2 (by decide +kernel)
 · exact S 9 125 3 (by decide +kernel)
 · exact S 9 125 4 (by decide +kernel)
 · exact S 9 125 5 (by decide +kernel)
theorem q9_126:ThresholdAt 9 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 126 0 (by decide +kernel)
 · exact S 9 126 1 (by decide +kernel)
 · exact S 9 126 2 (by decide +kernel)
 · exact S 9 126 3 (by decide +kernel)
 · exact S 9 126 4 (by decide +kernel)
 · exact S 9 126 5 (by decide +kernel)
theorem q9_127:ThresholdAt 9 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 127 0 (by decide +kernel)
 · exact S 9 127 1 (by decide +kernel)
 · exact S 9 127 2 (by decide +kernel)
 · exact S 9 127 3 (by decide +kernel)
 · exact S 9 127 4 (by decide +kernel)
 · exact S 9 127 5 (by decide +kernel)
theorem q9_128:ThresholdAt 9 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 128 0 (by decide +kernel)
 · exact S 9 128 1 (by decide +kernel)
 · exact S 9 128 2 (by decide +kernel)
 · exact S 9 128 3 (by decide +kernel)
 · exact S 9 128 4 (by decide +kernel)
 · exact S 9 128 5 (by decide +kernel)
theorem q9_129:ThresholdAt 9 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 129 0 (by decide +kernel)
 · exact S 9 129 1 (by decide +kernel)
 · exact S 9 129 2 (by decide +kernel)
 · exact S 9 129 3 (by decide +kernel)
 · exact S 9 129 4 (by decide +kernel)
 · exact S 9 129 5 (by decide +kernel)
theorem q9_130:ThresholdAt 9 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 130 0 (by decide +kernel)
 · exact S 9 130 1 (by decide +kernel)
 · exact S 9 130 2 (by decide +kernel)
 · exact S 9 130 3 (by decide +kernel)
 · exact S 9 130 4 (by decide +kernel)
 · exact S 9 130 5 (by decide +kernel)
theorem q9_131:ThresholdAt 9 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 131 0 (by decide +kernel)
 · exact S 9 131 1 (by decide +kernel)
 · exact S 9 131 2 (by decide +kernel)
 · exact S 9 131 3 (by decide +kernel)
 · exact S 9 131 4 (by decide +kernel)
 · exact S 9 131 5 (by decide +kernel)
theorem q9_132:ThresholdAt 9 132:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 132 0 (by decide +kernel)
 · exact S 9 132 1 (by decide +kernel)
 · exact S 9 132 2 (by decide +kernel)
 · exact S 9 132 3 (by decide +kernel)
 · exact S 9 132 4 (by decide +kernel)
 · exact S 9 132 5 (by decide +kernel)
theorem q9_133:ThresholdAt 9 133:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 9 133 0 (by decide +kernel)
 · exact S 9 133 1 (by decide +kernel)
 · exact S 9 133 2 (by decide +kernel)
 · exact S 9 133 3 (by decide +kernel)
 · exact S 9 133 4 (by decide +kernel)
 · exact S 9 133 5 (by decide +kernel)
theorem checkedR9:∀ V ∈ List.range 134,ThresholdAt 9 V:=by
  intro V hV
  have hv:V < 134:=List.mem_range.mp hV
  by_cases h0_134:V < 67
  · by_cases h0_67:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q9_0
              · have he:V = 1:=by omega
                subst V
                exact q9_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q9_2
              · have he:V = 3:=by omega
                subst V
                exact q9_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q9_4
              · have he:V = 5:=by omega
                subst V
                exact q9_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q9_6
              · have he:V = 7:=by omega
                subst V
                exact q9_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q9_8
              · have he:V = 9:=by omega
                subst V
                exact q9_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q9_10
              · have he:V = 11:=by omega
                subst V
                exact q9_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q9_12
              · have he:V = 13:=by omega
                subst V
                exact q9_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q9_14
              · have he:V = 15:=by omega
                subst V
                exact q9_15
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q9_16
              · have he:V = 17:=by omega
                subst V
                exact q9_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q9_18
              · have he:V = 19:=by omega
                subst V
                exact q9_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q9_20
              · have he:V = 21:=by omega
                subst V
                exact q9_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q9_22
              · have he:V = 23:=by omega
                subst V
                exact q9_23
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q9_24
              · have he:V = 25:=by omega
                subst V
                exact q9_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q9_26
              · have he:V = 27:=by omega
                subst V
                exact q9_27
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q9_28
              · have he:V = 29:=by omega
                subst V
                exact q9_29
            · by_cases h30_33:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q9_30
              · by_cases h31_33:V < 32
                · have he:V = 31:=by omega
                  subst V
                  exact q9_31
                · have he:V = 32:=by omega
                  subst V
                  exact q9_32
    · by_cases h33_67:V < 50
      · by_cases h33_50:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q9_33
              · have he:V = 34:=by omega
                subst V
                exact q9_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q9_35
              · have he:V = 36:=by omega
                subst V
                exact q9_36
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q9_37
              · have he:V = 38:=by omega
                subst V
                exact q9_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q9_39
              · have he:V = 40:=by omega
                subst V
                exact q9_40
        · by_cases h41_50:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q9_41
              · have he:V = 42:=by omega
                subst V
                exact q9_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q9_43
              · have he:V = 44:=by omega
                subst V
                exact q9_44
          · by_cases h45_50:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q9_45
              · have he:V = 46:=by omega
                subst V
                exact q9_46
            · by_cases h47_50:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q9_47
              · by_cases h48_50:V < 49
                · have he:V = 48:=by omega
                  subst V
                  exact q9_48
                · have he:V = 49:=by omega
                  subst V
                  exact q9_49
      · by_cases h50_67:V < 58
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q9_50
              · have he:V = 51:=by omega
                subst V
                exact q9_51
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q9_52
              · have he:V = 53:=by omega
                subst V
                exact q9_53
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q9_54
              · have he:V = 55:=by omega
                subst V
                exact q9_55
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q9_56
              · have he:V = 57:=by omega
                subst V
                exact q9_57
        · by_cases h58_67:V < 62
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q9_58
              · have he:V = 59:=by omega
                subst V
                exact q9_59
            · by_cases h60_62:V < 61
              · have he:V = 60:=by omega
                subst V
                exact q9_60
              · have he:V = 61:=by omega
                subst V
                exact q9_61
          · by_cases h62_67:V < 64
            · by_cases h62_64:V < 63
              · have he:V = 62:=by omega
                subst V
                exact q9_62
              · have he:V = 63:=by omega
                subst V
                exact q9_63
            · by_cases h64_67:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q9_64
              · by_cases h65_67:V < 66
                · have he:V = 65:=by omega
                  subst V
                  exact q9_65
                · have he:V = 66:=by omega
                  subst V
                  exact q9_66
  · by_cases h67_134:V < 100
    · by_cases h67_100:V < 83
      · by_cases h67_83:V < 75
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q9_67
              · have he:V = 68:=by omega
                subst V
                exact q9_68
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q9_69
              · have he:V = 70:=by omega
                subst V
                exact q9_70
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q9_71
              · have he:V = 72:=by omega
                subst V
                exact q9_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q9_73
              · have he:V = 74:=by omega
                subst V
                exact q9_74
        · by_cases h75_83:V < 79
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q9_75
              · have he:V = 76:=by omega
                subst V
                exact q9_76
            · by_cases h77_79:V < 78
              · have he:V = 77:=by omega
                subst V
                exact q9_77
              · have he:V = 78:=by omega
                subst V
                exact q9_78
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have he:V = 79:=by omega
                subst V
                exact q9_79
              · have he:V = 80:=by omega
                subst V
                exact q9_80
            · by_cases h81_83:V < 82
              · have he:V = 81:=by omega
                subst V
                exact q9_81
              · have he:V = 82:=by omega
                subst V
                exact q9_82
      · by_cases h83_100:V < 91
        · by_cases h83_91:V < 87
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have he:V = 83:=by omega
                subst V
                exact q9_83
              · have he:V = 84:=by omega
                subst V
                exact q9_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q9_85
              · have he:V = 86:=by omega
                subst V
                exact q9_86
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q9_87
              · have he:V = 88:=by omega
                subst V
                exact q9_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q9_89
              · have he:V = 90:=by omega
                subst V
                exact q9_90
        · by_cases h91_100:V < 95
          · by_cases h91_95:V < 93
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q9_91
              · have he:V = 92:=by omega
                subst V
                exact q9_92
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q9_93
              · have he:V = 94:=by omega
                subst V
                exact q9_94
          · by_cases h95_100:V < 97
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q9_95
              · have he:V = 96:=by omega
                subst V
                exact q9_96
            · by_cases h97_100:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q9_97
              · by_cases h98_100:V < 99
                · have he:V = 98:=by omega
                  subst V
                  exact q9_98
                · have he:V = 99:=by omega
                  subst V
                  exact q9_99
    · by_cases h100_134:V < 117
      · by_cases h100_117:V < 108
        · by_cases h100_108:V < 104
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q9_100
              · have he:V = 101:=by omega
                subst V
                exact q9_101
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q9_102
              · have he:V = 103:=by omega
                subst V
                exact q9_103
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q9_104
              · have he:V = 105:=by omega
                subst V
                exact q9_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q9_106
              · have he:V = 107:=by omega
                subst V
                exact q9_107
        · by_cases h108_117:V < 112
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q9_108
              · have he:V = 109:=by omega
                subst V
                exact q9_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q9_110
              · have he:V = 111:=by omega
                subst V
                exact q9_111
          · by_cases h112_117:V < 114
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q9_112
              · have he:V = 113:=by omega
                subst V
                exact q9_113
            · by_cases h114_117:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q9_114
              · by_cases h115_117:V < 116
                · have he:V = 115:=by omega
                  subst V
                  exact q9_115
                · have he:V = 116:=by omega
                  subst V
                  exact q9_116
      · by_cases h117_134:V < 125
        · by_cases h117_125:V < 121
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q9_117
              · have he:V = 118:=by omega
                subst V
                exact q9_118
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q9_119
              · have he:V = 120:=by omega
                subst V
                exact q9_120
          · by_cases h121_125:V < 123
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q9_121
              · have he:V = 122:=by omega
                subst V
                exact q9_122
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q9_123
              · have he:V = 124:=by omega
                subst V
                exact q9_124
        · by_cases h125_134:V < 129
          · by_cases h125_129:V < 127
            · by_cases h125_127:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q9_125
              · have he:V = 126:=by omega
                subst V
                exact q9_126
            · by_cases h127_129:V < 128
              · have he:V = 127:=by omega
                subst V
                exact q9_127
              · have he:V = 128:=by omega
                subst V
                exact q9_128
          · by_cases h129_134:V < 131
            · by_cases h129_131:V < 130
              · have he:V = 129:=by omega
                subst V
                exact q9_129
              · have he:V = 130:=by omega
                subst V
                exact q9_130
            · by_cases h131_134:V < 132
              · have he:V = 131:=by omega
                subst V
                exact q9_131
              · by_cases h132_134:V < 133
                · have he:V = 132:=by omega
                  subst V
                  exact q9_132
                · have he:V = 133:=by omega
                  subst V
                  exact q9_133
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
