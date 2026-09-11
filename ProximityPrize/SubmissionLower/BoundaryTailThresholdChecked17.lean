import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked16

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q17_0:ThresholdAt 17 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 0 0 (by decide +kernel)
 · exact S 17 0 1 (by decide +kernel)
 · exact S 17 0 2 (by decide +kernel)
 · exact S 17 0 3 (by decide +kernel)
 · exact S 17 0 4 (by decide +kernel)
 · exact S 17 0 5 (by decide +kernel)
theorem q17_1:ThresholdAt 17 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 1 0 (by decide +kernel)
 · exact S 17 1 1 (by decide +kernel)
 · exact S 17 1 2 (by decide +kernel)
 · exact S 17 1 3 (by decide +kernel)
 · exact S 17 1 4 (by decide +kernel)
 · exact S 17 1 5 (by decide +kernel)
theorem q17_2:ThresholdAt 17 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 2 0 (by decide +kernel)
 · exact S 17 2 1 (by decide +kernel)
 · exact S 17 2 2 (by decide +kernel)
 · exact S 17 2 3 (by decide +kernel)
 · exact S 17 2 4 (by decide +kernel)
 · exact S 17 2 5 (by decide +kernel)
theorem q17_3:ThresholdAt 17 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 3 0 (by decide +kernel)
 · exact S 17 3 1 (by decide +kernel)
 · exact S 17 3 2 (by decide +kernel)
 · exact S 17 3 3 (by decide +kernel)
 · exact S 17 3 4 (by decide +kernel)
 · exact S 17 3 5 (by decide +kernel)
theorem q17_4:ThresholdAt 17 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 4 0 (by decide +kernel)
 · exact S 17 4 1 (by decide +kernel)
 · exact S 17 4 2 (by decide +kernel)
 · exact S 17 4 3 (by decide +kernel)
 · exact S 17 4 4 (by decide +kernel)
 · exact S 17 4 5 (by decide +kernel)
theorem q17_5:ThresholdAt 17 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 5 0 (by decide +kernel)
 · exact S 17 5 1 (by decide +kernel)
 · exact S 17 5 2 (by decide +kernel)
 · exact S 17 5 3 (by decide +kernel)
 · exact S 17 5 4 (by decide +kernel)
 · exact S 17 5 5 (by decide +kernel)
theorem q17_6:ThresholdAt 17 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 6 0 (by decide +kernel)
 · exact S 17 6 1 (by decide +kernel)
 · exact S 17 6 2 (by decide +kernel)
 · exact S 17 6 3 (by decide +kernel)
 · exact S 17 6 4 (by decide +kernel)
 · exact S 17 6 5 (by decide +kernel)
theorem q17_7:ThresholdAt 17 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 7 0 (by decide +kernel)
 · exact S 17 7 1 (by decide +kernel)
 · exact S 17 7 2 (by decide +kernel)
 · exact S 17 7 3 (by decide +kernel)
 · exact S 17 7 4 (by decide +kernel)
 · exact S 17 7 5 (by decide +kernel)
theorem q17_8:ThresholdAt 17 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 8 0 (by decide +kernel)
 · exact S 17 8 1 (by decide +kernel)
 · exact S 17 8 2 (by decide +kernel)
 · exact S 17 8 3 (by decide +kernel)
 · exact S 17 8 4 (by decide +kernel)
 · exact S 17 8 5 (by decide +kernel)
theorem q17_9:ThresholdAt 17 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 9 0 (by decide +kernel)
 · exact S 17 9 1 (by decide +kernel)
 · exact S 17 9 2 (by decide +kernel)
 · exact S 17 9 3 (by decide +kernel)
 · exact S 17 9 4 (by decide +kernel)
 · exact S 17 9 5 (by decide +kernel)
theorem q17_10:ThresholdAt 17 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 10 0 (by decide +kernel)
 · exact S 17 10 1 (by decide +kernel)
 · exact S 17 10 2 (by decide +kernel)
 · exact S 17 10 3 (by decide +kernel)
 · exact S 17 10 4 (by decide +kernel)
 · exact S 17 10 5 (by decide +kernel)
theorem q17_11:ThresholdAt 17 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 11 0 (by decide +kernel)
 · exact S 17 11 1 (by decide +kernel)
 · exact S 17 11 2 (by decide +kernel)
 · exact S 17 11 3 (by decide +kernel)
 · exact S 17 11 4 (by decide +kernel)
 · exact S 17 11 5 (by decide +kernel)
theorem q17_12:ThresholdAt 17 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 12 0 (by decide +kernel)
 · exact S 17 12 1 (by decide +kernel)
 · exact S 17 12 2 (by decide +kernel)
 · exact S 17 12 3 (by decide +kernel)
 · exact S 17 12 4 (by decide +kernel)
 · exact S 17 12 5 (by decide +kernel)
theorem q17_13:ThresholdAt 17 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 13 0 (by decide +kernel)
 · exact S 17 13 1 (by decide +kernel)
 · exact S 17 13 2 (by decide +kernel)
 · exact S 17 13 3 (by decide +kernel)
 · exact S 17 13 4 (by decide +kernel)
 · exact S 17 13 5 (by decide +kernel)
theorem q17_14:ThresholdAt 17 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 14 0 (by decide +kernel)
 · exact S 17 14 1 (by decide +kernel)
 · exact S 17 14 2 (by decide +kernel)
 · exact S 17 14 3 (by decide +kernel)
 · exact S 17 14 4 (by decide +kernel)
 · exact S 17 14 5 (by decide +kernel)
theorem q17_15:ThresholdAt 17 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 15 0 (by decide +kernel)
 · exact S 17 15 1 (by decide +kernel)
 · exact S 17 15 2 (by decide +kernel)
 · exact S 17 15 3 (by decide +kernel)
 · exact S 17 15 4 (by decide +kernel)
 · exact S 17 15 5 (by decide +kernel)
theorem q17_16:ThresholdAt 17 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 16 0 (by decide +kernel)
 · exact S 17 16 1 (by decide +kernel)
 · exact S 17 16 2 (by decide +kernel)
 · exact S 17 16 3 (by decide +kernel)
 · exact S 17 16 4 (by decide +kernel)
 · exact S 17 16 5 (by decide +kernel)
theorem q17_17:ThresholdAt 17 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 17 0 (by decide +kernel)
 · exact S 17 17 1 (by decide +kernel)
 · exact S 17 17 2 (by decide +kernel)
 · exact S 17 17 3 (by decide +kernel)
 · exact S 17 17 4 (by decide +kernel)
 · exact S 17 17 5 (by decide +kernel)
theorem q17_18:ThresholdAt 17 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 18 0 (by decide +kernel)
 · exact S 17 18 1 (by decide +kernel)
 · exact S 17 18 2 (by decide +kernel)
 · exact S 17 18 3 (by decide +kernel)
 · exact S 17 18 4 (by decide +kernel)
 · exact S 17 18 5 (by decide +kernel)
theorem q17_19:ThresholdAt 17 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 19 0 (by decide +kernel)
 · exact S 17 19 1 (by decide +kernel)
 · exact S 17 19 2 (by decide +kernel)
 · exact S 17 19 3 (by decide +kernel)
 · exact S 17 19 4 (by decide +kernel)
 · exact S 17 19 5 (by decide +kernel)
theorem q17_20:ThresholdAt 17 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 20 0 (by decide +kernel)
 · exact S 17 20 1 (by decide +kernel)
 · exact S 17 20 2 (by decide +kernel)
 · exact S 17 20 3 (by decide +kernel)
 · exact S 17 20 4 (by decide +kernel)
 · exact S 17 20 5 (by decide +kernel)
theorem q17_21:ThresholdAt 17 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 21 0 (by decide +kernel)
 · exact S 17 21 1 (by decide +kernel)
 · exact S 17 21 2 (by decide +kernel)
 · exact S 17 21 3 (by decide +kernel)
 · exact S 17 21 4 (by decide +kernel)
 · exact S 17 21 5 (by decide +kernel)
theorem q17_22:ThresholdAt 17 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 22 0 (by decide +kernel)
 · exact S 17 22 1 (by decide +kernel)
 · exact S 17 22 2 (by decide +kernel)
 · exact S 17 22 3 (by decide +kernel)
 · exact S 17 22 4 (by decide +kernel)
 · exact S 17 22 5 (by decide +kernel)
theorem q17_23:ThresholdAt 17 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 23 0 (by decide +kernel)
 · exact S 17 23 1 (by decide +kernel)
 · exact S 17 23 2 (by decide +kernel)
 · exact S 17 23 3 (by decide +kernel)
 · exact S 17 23 4 (by decide +kernel)
 · exact S 17 23 5 (by decide +kernel)
theorem q17_24:ThresholdAt 17 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 24 0 (by decide +kernel)
 · exact S 17 24 1 (by decide +kernel)
 · exact S 17 24 2 (by decide +kernel)
 · exact S 17 24 3 (by decide +kernel)
 · exact S 17 24 4 (by decide +kernel)
 · exact S 17 24 5 (by decide +kernel)
theorem q17_25:ThresholdAt 17 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 25 0 (by decide +kernel)
 · exact S 17 25 1 (by decide +kernel)
 · exact S 17 25 2 (by decide +kernel)
 · exact S 17 25 3 (by decide +kernel)
 · exact S 17 25 4 (by decide +kernel)
 · exact S 17 25 5 (by decide +kernel)
theorem q17_26:ThresholdAt 17 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 26 0 (by decide +kernel)
 · exact S 17 26 1 (by decide +kernel)
 · exact S 17 26 2 (by decide +kernel)
 · exact S 17 26 3 (by decide +kernel)
 · exact S 17 26 4 (by decide +kernel)
 · exact S 17 26 5 (by decide +kernel)
theorem q17_27:ThresholdAt 17 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 27 0 (by decide +kernel)
 · exact S 17 27 1 (by decide +kernel)
 · exact S 17 27 2 (by decide +kernel)
 · exact S 17 27 3 (by decide +kernel)
 · exact S 17 27 4 (by decide +kernel)
 · exact S 17 27 5 (by decide +kernel)
theorem q17_28:ThresholdAt 17 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 28 0 (by decide +kernel)
 · exact S 17 28 1 (by decide +kernel)
 · exact S 17 28 2 (by decide +kernel)
 · exact S 17 28 3 (by decide +kernel)
 · exact S 17 28 4 (by decide +kernel)
 · exact S 17 28 5 (by decide +kernel)
theorem q17_29:ThresholdAt 17 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 29 0 (by decide +kernel)
 · exact S 17 29 1 (by decide +kernel)
 · exact S 17 29 2 (by decide +kernel)
 · exact S 17 29 3 (by decide +kernel)
 · exact S 17 29 4 (by decide +kernel)
 · exact S 17 29 5 (by decide +kernel)
theorem q17_30:ThresholdAt 17 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 30 0 (by decide +kernel)
 · exact S 17 30 1 (by decide +kernel)
 · exact S 17 30 2 (by decide +kernel)
 · exact S 17 30 3 (by decide +kernel)
 · exact S 17 30 4 (by decide +kernel)
 · exact S 17 30 5 (by decide +kernel)
theorem q17_31:ThresholdAt 17 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 31 0 (by decide +kernel)
 · exact S 17 31 1 (by decide +kernel)
 · exact S 17 31 2 (by decide +kernel)
 · exact S 17 31 3 (by decide +kernel)
 · exact S 17 31 4 (by decide +kernel)
 · exact S 17 31 5 (by decide +kernel)
theorem q17_32:ThresholdAt 17 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 32 0 (by decide +kernel)
 · exact S 17 32 1 (by decide +kernel)
 · exact S 17 32 2 (by decide +kernel)
 · exact S 17 32 3 (by decide +kernel)
 · exact S 17 32 4 (by decide +kernel)
 · exact S 17 32 5 (by decide +kernel)
theorem q17_33:ThresholdAt 17 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 33 0 (by decide +kernel)
 · exact S 17 33 1 (by decide +kernel)
 · exact S 17 33 2 (by decide +kernel)
 · exact S 17 33 3 (by decide +kernel)
 · exact S 17 33 4 (by decide +kernel)
 · exact S 17 33 5 (by decide +kernel)
theorem q17_34:ThresholdAt 17 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 34 0 (by decide +kernel)
 · exact S 17 34 1 (by decide +kernel)
 · exact S 17 34 2 (by decide +kernel)
 · exact S 17 34 3 (by decide +kernel)
 · exact S 17 34 4 (by decide +kernel)
 · exact S 17 34 5 (by decide +kernel)
theorem q17_35:ThresholdAt 17 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 35 0 (by decide +kernel)
 · exact S 17 35 1 (by decide +kernel)
 · exact S 17 35 2 (by decide +kernel)
 · exact S 17 35 3 (by decide +kernel)
 · exact S 17 35 4 (by decide +kernel)
 · exact S 17 35 5 (by decide +kernel)
theorem q17_36:ThresholdAt 17 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 36 0 (by decide +kernel)
 · exact S 17 36 1 (by decide +kernel)
 · exact S 17 36 2 (by decide +kernel)
 · exact S 17 36 3 (by decide +kernel)
 · exact S 17 36 4 (by decide +kernel)
 · exact S 17 36 5 (by decide +kernel)
theorem q17_37:ThresholdAt 17 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 37 0 (by decide +kernel)
 · exact S 17 37 1 (by decide +kernel)
 · exact S 17 37 2 (by decide +kernel)
 · exact S 17 37 3 (by decide +kernel)
 · exact S 17 37 4 (by decide +kernel)
 · exact S 17 37 5 (by decide +kernel)
theorem q17_38:ThresholdAt 17 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 38 0 (by decide +kernel)
 · exact S 17 38 1 (by decide +kernel)
 · exact S 17 38 2 (by decide +kernel)
 · exact S 17 38 3 (by decide +kernel)
 · exact S 17 38 4 (by decide +kernel)
 · exact S 17 38 5 (by decide +kernel)
theorem q17_39:ThresholdAt 17 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 39 0 (by decide +kernel)
 · exact S 17 39 1 (by decide +kernel)
 · exact S 17 39 2 (by decide +kernel)
 · exact S 17 39 3 (by decide +kernel)
 · exact S 17 39 4 (by decide +kernel)
 · exact S 17 39 5 (by decide +kernel)
theorem q17_40:ThresholdAt 17 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 40 0 (by decide +kernel)
 · exact S 17 40 1 (by decide +kernel)
 · exact S 17 40 2 (by decide +kernel)
 · exact S 17 40 3 (by decide +kernel)
 · exact S 17 40 4 (by decide +kernel)
 · exact S 17 40 5 (by decide +kernel)
theorem q17_41:ThresholdAt 17 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 41 0 (by decide +kernel)
 · exact S 17 41 1 (by decide +kernel)
 · exact S 17 41 2 (by decide +kernel)
 · exact S 17 41 3 (by decide +kernel)
 · exact S 17 41 4 (by decide +kernel)
 · exact S 17 41 5 (by decide +kernel)
theorem q17_42:ThresholdAt 17 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 42 0 (by decide +kernel)
 · exact S 17 42 1 (by decide +kernel)
 · exact S 17 42 2 (by decide +kernel)
 · exact S 17 42 3 (by decide +kernel)
 · exact S 17 42 4 (by decide +kernel)
 · exact S 17 42 5 (by decide +kernel)
theorem q17_43:ThresholdAt 17 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 43 0 (by decide +kernel)
 · exact S 17 43 1 (by decide +kernel)
 · exact S 17 43 2 (by decide +kernel)
 · exact S 17 43 3 (by decide +kernel)
 · exact S 17 43 4 (by decide +kernel)
 · exact S 17 43 5 (by decide +kernel)
theorem q17_44:ThresholdAt 17 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 44 0 (by decide +kernel)
 · exact S 17 44 1 (by decide +kernel)
 · exact S 17 44 2 (by decide +kernel)
 · exact S 17 44 3 (by decide +kernel)
 · exact S 17 44 4 (by decide +kernel)
 · exact S 17 44 5 (by decide +kernel)
theorem q17_45:ThresholdAt 17 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 45 0 (by decide +kernel)
 · exact S 17 45 1 (by decide +kernel)
 · exact S 17 45 2 (by decide +kernel)
 · exact S 17 45 3 (by decide +kernel)
 · exact S 17 45 4 (by decide +kernel)
 · exact S 17 45 5 (by decide +kernel)
theorem q17_46:ThresholdAt 17 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 46 0 (by decide +kernel)
 · exact S 17 46 1 (by decide +kernel)
 · exact S 17 46 2 (by decide +kernel)
 · exact S 17 46 3 (by decide +kernel)
 · exact S 17 46 4 (by decide +kernel)
 · exact S 17 46 5 (by decide +kernel)
theorem q17_47:ThresholdAt 17 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 47 0 (by decide +kernel)
 · exact S 17 47 1 (by decide +kernel)
 · exact S 17 47 2 (by decide +kernel)
 · exact S 17 47 3 (by decide +kernel)
 · exact S 17 47 4 (by decide +kernel)
 · exact S 17 47 5 (by decide +kernel)
theorem q17_48:ThresholdAt 17 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 48 0 (by decide +kernel)
 · exact S 17 48 1 (by decide +kernel)
 · exact S 17 48 2 (by decide +kernel)
 · exact S 17 48 3 (by decide +kernel)
 · exact S 17 48 4 (by decide +kernel)
 · exact S 17 48 5 (by decide +kernel)
theorem q17_49:ThresholdAt 17 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 49 0 (by decide +kernel)
 · exact S 17 49 1 (by decide +kernel)
 · exact S 17 49 2 (by decide +kernel)
 · exact S 17 49 3 (by decide +kernel)
 · exact S 17 49 4 (by decide +kernel)
 · exact S 17 49 5 (by decide +kernel)
theorem q17_50:ThresholdAt 17 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 50 0 (by decide +kernel)
 · exact S 17 50 1 (by decide +kernel)
 · exact S 17 50 2 (by decide +kernel)
 · exact S 17 50 3 (by decide +kernel)
 · exact S 17 50 4 (by decide +kernel)
 · exact S 17 50 5 (by decide +kernel)
theorem q17_51:ThresholdAt 17 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 51 0 (by decide +kernel)
 · exact S 17 51 1 (by decide +kernel)
 · exact S 17 51 2 (by decide +kernel)
 · exact S 17 51 3 (by decide +kernel)
 · exact S 17 51 4 (by decide +kernel)
 · exact S 17 51 5 (by decide +kernel)
theorem q17_52:ThresholdAt 17 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 52 0 (by decide +kernel)
 · exact S 17 52 1 (by decide +kernel)
 · exact S 17 52 2 (by decide +kernel)
 · exact S 17 52 3 (by decide +kernel)
 · exact S 17 52 4 (by decide +kernel)
 · exact S 17 52 5 (by decide +kernel)
theorem q17_53:ThresholdAt 17 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 53 0 (by decide +kernel)
 · exact S 17 53 1 (by decide +kernel)
 · exact S 17 53 2 (by decide +kernel)
 · exact S 17 53 3 (by decide +kernel)
 · exact S 17 53 4 (by decide +kernel)
 · exact S 17 53 5 (by decide +kernel)
theorem q17_54:ThresholdAt 17 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 54 0 (by decide +kernel)
 · exact S 17 54 1 (by decide +kernel)
 · exact S 17 54 2 (by decide +kernel)
 · exact S 17 54 3 (by decide +kernel)
 · exact S 17 54 4 (by decide +kernel)
 · exact S 17 54 5 (by decide +kernel)
theorem q17_55:ThresholdAt 17 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 55 0 (by decide +kernel)
 · exact S 17 55 1 (by decide +kernel)
 · exact S 17 55 2 (by decide +kernel)
 · exact S 17 55 3 (by decide +kernel)
 · exact S 17 55 4 (by decide +kernel)
 · exact S 17 55 5 (by decide +kernel)
theorem q17_56:ThresholdAt 17 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 56 0 (by decide +kernel)
 · exact S 17 56 1 (by decide +kernel)
 · exact S 17 56 2 (by decide +kernel)
 · exact S 17 56 3 (by decide +kernel)
 · exact S 17 56 4 (by decide +kernel)
 · exact S 17 56 5 (by decide +kernel)
theorem q17_57:ThresholdAt 17 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 57 0 (by decide +kernel)
 · exact S 17 57 1 (by decide +kernel)
 · exact S 17 57 2 (by decide +kernel)
 · exact S 17 57 3 (by decide +kernel)
 · exact S 17 57 4 (by decide +kernel)
 · exact S 17 57 5 (by decide +kernel)
theorem q17_58:ThresholdAt 17 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 58 0 (by decide +kernel)
 · exact S 17 58 1 (by decide +kernel)
 · exact S 17 58 2 (by decide +kernel)
 · exact S 17 58 3 (by decide +kernel)
 · exact S 17 58 4 (by decide +kernel)
 · exact S 17 58 5 (by decide +kernel)
theorem q17_59:ThresholdAt 17 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 59 0 (by decide +kernel)
 · exact S 17 59 1 (by decide +kernel)
 · exact S 17 59 2 (by decide +kernel)
 · exact S 17 59 3 (by decide +kernel)
 · exact S 17 59 4 (by decide +kernel)
 · exact S 17 59 5 (by decide +kernel)
theorem q17_60:ThresholdAt 17 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 60 0 (by decide +kernel)
 · exact S 17 60 1 (by decide +kernel)
 · exact S 17 60 2 (by decide +kernel)
 · exact S 17 60 3 (by decide +kernel)
 · exact S 17 60 4 (by decide +kernel)
 · exact S 17 60 5 (by decide +kernel)
theorem q17_61:ThresholdAt 17 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 61 0 (by decide +kernel)
 · exact S 17 61 1 (by decide +kernel)
 · exact S 17 61 2 (by decide +kernel)
 · exact S 17 61 3 (by decide +kernel)
 · exact S 17 61 4 (by decide +kernel)
 · exact S 17 61 5 (by decide +kernel)
theorem q17_62:ThresholdAt 17 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 62 0 (by decide +kernel)
 · exact S 17 62 1 (by decide +kernel)
 · exact S 17 62 2 (by decide +kernel)
 · exact S 17 62 3 (by decide +kernel)
 · exact S 17 62 4 (by decide +kernel)
 · exact S 17 62 5 (by decide +kernel)
theorem q17_63:ThresholdAt 17 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 63 0 (by decide +kernel)
 · exact S 17 63 1 (by decide +kernel)
 · exact S 17 63 2 (by decide +kernel)
 · exact S 17 63 3 (by decide +kernel)
 · exact S 17 63 4 (by decide +kernel)
 · exact S 17 63 5 (by decide +kernel)
theorem q17_64:ThresholdAt 17 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 64 0 (by decide +kernel)
 · exact S 17 64 1 (by decide +kernel)
 · exact S 17 64 2 (by decide +kernel)
 · exact S 17 64 3 (by decide +kernel)
 · exact S 17 64 4 (by decide +kernel)
 · exact S 17 64 5 (by decide +kernel)
theorem q17_65:ThresholdAt 17 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 65 0 (by decide +kernel)
 · exact S 17 65 1 (by decide +kernel)
 · exact S 17 65 2 (by decide +kernel)
 · exact S 17 65 3 (by decide +kernel)
 · exact S 17 65 4 (by decide +kernel)
 · exact S 17 65 5 (by decide +kernel)
theorem q17_66:ThresholdAt 17 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 66 0 (by decide +kernel)
 · exact S 17 66 1 (by decide +kernel)
 · exact S 17 66 2 (by decide +kernel)
 · exact S 17 66 3 (by decide +kernel)
 · exact S 17 66 4 (by decide +kernel)
 · exact S 17 66 5 (by decide +kernel)
theorem q17_67:ThresholdAt 17 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 67 0 (by decide +kernel)
 · exact S 17 67 1 (by decide +kernel)
 · exact S 17 67 2 (by decide +kernel)
 · exact S 17 67 3 (by decide +kernel)
 · exact S 17 67 4 (by decide +kernel)
 · exact S 17 67 5 (by decide +kernel)
theorem q17_68:ThresholdAt 17 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 68 0 (by decide +kernel)
 · exact S 17 68 1 (by decide +kernel)
 · exact S 17 68 2 (by decide +kernel)
 · exact S 17 68 3 (by decide +kernel)
 · exact S 17 68 4 (by decide +kernel)
 · exact S 17 68 5 (by decide +kernel)
theorem q17_69:ThresholdAt 17 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 69 0 (by decide +kernel)
 · exact S 17 69 1 (by decide +kernel)
 · exact S 17 69 2 (by decide +kernel)
 · exact S 17 69 3 (by decide +kernel)
 · exact S 17 69 4 (by decide +kernel)
 · exact S 17 69 5 (by decide +kernel)
theorem q17_70:ThresholdAt 17 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 70 0 (by decide +kernel)
 · exact S 17 70 1 (by decide +kernel)
 · exact S 17 70 2 (by decide +kernel)
 · exact S 17 70 3 (by decide +kernel)
 · exact S 17 70 4 (by decide +kernel)
 · exact S 17 70 5 (by decide +kernel)
theorem q17_71:ThresholdAt 17 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 71 0 (by decide +kernel)
 · exact S 17 71 1 (by decide +kernel)
 · exact S 17 71 2 (by decide +kernel)
 · exact S 17 71 3 (by decide +kernel)
 · exact S 17 71 4 (by decide +kernel)
 · exact S 17 71 5 (by decide +kernel)
theorem q17_72:ThresholdAt 17 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 72 0 (by decide +kernel)
 · exact S 17 72 1 (by decide +kernel)
 · exact S 17 72 2 (by decide +kernel)
 · exact S 17 72 3 (by decide +kernel)
 · exact S 17 72 4 (by decide +kernel)
 · exact S 17 72 5 (by decide +kernel)
theorem q17_73:ThresholdAt 17 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 73 0 (by decide +kernel)
 · exact S 17 73 1 (by decide +kernel)
 · exact S 17 73 2 (by decide +kernel)
 · exact S 17 73 3 (by decide +kernel)
 · exact S 17 73 4 (by decide +kernel)
 · exact S 17 73 5 (by decide +kernel)
theorem q17_74:ThresholdAt 17 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 74 0 (by decide +kernel)
 · exact S 17 74 1 (by decide +kernel)
 · exact S 17 74 2 (by decide +kernel)
 · exact S 17 74 3 (by decide +kernel)
 · exact S 17 74 4 (by decide +kernel)
 · exact S 17 74 5 (by decide +kernel)
theorem q17_75:ThresholdAt 17 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 75 0 (by decide +kernel)
 · exact S 17 75 1 (by decide +kernel)
 · exact S 17 75 2 (by decide +kernel)
 · exact S 17 75 3 (by decide +kernel)
 · exact S 17 75 4 (by decide +kernel)
 · exact S 17 75 5 (by decide +kernel)
theorem q17_76:ThresholdAt 17 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 76 0 (by decide +kernel)
 · exact S 17 76 1 (by decide +kernel)
 · exact S 17 76 2 (by decide +kernel)
 · exact S 17 76 3 (by decide +kernel)
 · exact S 17 76 4 (by decide +kernel)
 · exact S 17 76 5 (by decide +kernel)
theorem q17_77:ThresholdAt 17 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 77 0 (by decide +kernel)
 · exact S 17 77 1 (by decide +kernel)
 · exact S 17 77 2 (by decide +kernel)
 · exact S 17 77 3 (by decide +kernel)
 · exact S 17 77 4 (by decide +kernel)
 · exact S 17 77 5 (by decide +kernel)
theorem q17_78:ThresholdAt 17 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 78 0 (by decide +kernel)
 · exact S 17 78 1 (by decide +kernel)
 · exact S 17 78 2 (by decide +kernel)
 · exact S 17 78 3 (by decide +kernel)
 · exact S 17 78 4 (by decide +kernel)
 · exact S 17 78 5 (by decide +kernel)
theorem q17_79:ThresholdAt 17 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 79 0 (by decide +kernel)
 · exact S 17 79 1 (by decide +kernel)
 · exact S 17 79 2 (by decide +kernel)
 · exact S 17 79 3 (by decide +kernel)
 · exact S 17 79 4 (by decide +kernel)
 · exact S 17 79 5 (by decide +kernel)
theorem q17_80:ThresholdAt 17 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 80 0 (by decide +kernel)
 · exact S 17 80 1 (by decide +kernel)
 · exact S 17 80 2 (by decide +kernel)
 · exact S 17 80 3 (by decide +kernel)
 · exact S 17 80 4 (by decide +kernel)
 · exact S 17 80 5 (by decide +kernel)
theorem q17_81:ThresholdAt 17 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 81 0 (by decide +kernel)
 · exact S 17 81 1 (by decide +kernel)
 · exact S 17 81 2 (by decide +kernel)
 · exact S 17 81 3 (by decide +kernel)
 · exact S 17 81 4 (by decide +kernel)
 · exact S 17 81 5 (by decide +kernel)
theorem q17_82:ThresholdAt 17 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 82 0 (by decide +kernel)
 · exact S 17 82 1 (by decide +kernel)
 · exact S 17 82 2 (by decide +kernel)
 · exact S 17 82 3 (by decide +kernel)
 · exact S 17 82 4 (by decide +kernel)
 · exact S 17 82 5 (by decide +kernel)
theorem q17_83:ThresholdAt 17 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 83 0 (by decide +kernel)
 · exact S 17 83 1 (by decide +kernel)
 · exact S 17 83 2 (by decide +kernel)
 · exact S 17 83 3 (by decide +kernel)
 · exact S 17 83 4 (by decide +kernel)
 · exact S 17 83 5 (by decide +kernel)
theorem q17_84:ThresholdAt 17 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 84 0 (by decide +kernel)
 · exact S 17 84 1 (by decide +kernel)
 · exact S 17 84 2 (by decide +kernel)
 · exact S 17 84 3 (by decide +kernel)
 · exact S 17 84 4 (by decide +kernel)
 · exact S 17 84 5 (by decide +kernel)
theorem q17_85:ThresholdAt 17 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 85 0 (by decide +kernel)
 · exact S 17 85 1 (by decide +kernel)
 · exact S 17 85 2 (by decide +kernel)
 · exact S 17 85 3 (by decide +kernel)
 · exact S 17 85 4 (by decide +kernel)
 · exact S 17 85 5 (by decide +kernel)
theorem q17_86:ThresholdAt 17 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 86 0 (by decide +kernel)
 · exact S 17 86 1 (by decide +kernel)
 · exact S 17 86 2 (by decide +kernel)
 · exact S 17 86 3 (by decide +kernel)
 · exact S 17 86 4 (by decide +kernel)
 · exact S 17 86 5 (by decide +kernel)
theorem q17_87:ThresholdAt 17 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 87 0 (by decide +kernel)
 · exact S 17 87 1 (by decide +kernel)
 · exact S 17 87 2 (by decide +kernel)
 · exact S 17 87 3 (by decide +kernel)
 · exact S 17 87 4 (by decide +kernel)
 · exact S 17 87 5 (by decide +kernel)
theorem q17_88:ThresholdAt 17 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 88 0 (by decide +kernel)
 · exact S 17 88 1 (by decide +kernel)
 · exact S 17 88 2 (by decide +kernel)
 · exact S 17 88 3 (by decide +kernel)
 · exact S 17 88 4 (by decide +kernel)
 · exact S 17 88 5 (by decide +kernel)
theorem q17_89:ThresholdAt 17 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 89 0 (by decide +kernel)
 · exact S 17 89 1 (by decide +kernel)
 · exact S 17 89 2 (by decide +kernel)
 · exact S 17 89 3 (by decide +kernel)
 · exact S 17 89 4 (by decide +kernel)
 · exact S 17 89 5 (by decide +kernel)
theorem q17_90:ThresholdAt 17 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 90 0 (by decide +kernel)
 · exact S 17 90 1 (by decide +kernel)
 · exact S 17 90 2 (by decide +kernel)
 · exact S 17 90 3 (by decide +kernel)
 · exact S 17 90 4 (by decide +kernel)
 · exact S 17 90 5 (by decide +kernel)
theorem q17_91:ThresholdAt 17 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 91 0 (by decide +kernel)
 · exact S 17 91 1 (by decide +kernel)
 · exact S 17 91 2 (by decide +kernel)
 · exact S 17 91 3 (by decide +kernel)
 · exact S 17 91 4 (by decide +kernel)
 · exact S 17 91 5 (by decide +kernel)
theorem q17_92:ThresholdAt 17 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 92 0 (by decide +kernel)
 · exact S 17 92 1 (by decide +kernel)
 · exact S 17 92 2 (by decide +kernel)
 · exact S 17 92 3 (by decide +kernel)
 · exact S 17 92 4 (by decide +kernel)
 · exact S 17 92 5 (by decide +kernel)
theorem q17_93:ThresholdAt 17 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 93 0 (by decide +kernel)
 · exact S 17 93 1 (by decide +kernel)
 · exact S 17 93 2 (by decide +kernel)
 · exact S 17 93 3 (by decide +kernel)
 · exact S 17 93 4 (by decide +kernel)
 · exact S 17 93 5 (by decide +kernel)
theorem q17_94:ThresholdAt 17 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 94 0 (by decide +kernel)
 · exact S 17 94 1 (by decide +kernel)
 · exact S 17 94 2 (by decide +kernel)
 · exact S 17 94 3 (by decide +kernel)
 · exact S 17 94 4 (by decide +kernel)
 · exact S 17 94 5 (by decide +kernel)
theorem q17_95:ThresholdAt 17 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 95 0 (by decide +kernel)
 · exact S 17 95 1 (by decide +kernel)
 · exact S 17 95 2 (by decide +kernel)
 · exact S 17 95 3 (by decide +kernel)
 · exact S 17 95 4 (by decide +kernel)
 · exact S 17 95 5 (by decide +kernel)
theorem q17_96:ThresholdAt 17 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 96 0 (by decide +kernel)
 · exact S 17 96 1 (by decide +kernel)
 · exact S 17 96 2 (by decide +kernel)
 · exact S 17 96 3 (by decide +kernel)
 · exact S 17 96 4 (by decide +kernel)
 · exact S 17 96 5 (by decide +kernel)
theorem q17_97:ThresholdAt 17 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 97 0 (by decide +kernel)
 · exact S 17 97 1 (by decide +kernel)
 · exact S 17 97 2 (by decide +kernel)
 · exact S 17 97 3 (by decide +kernel)
 · exact S 17 97 4 (by decide +kernel)
 · exact S 17 97 5 (by decide +kernel)
theorem q17_98:ThresholdAt 17 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 98 0 (by decide +kernel)
 · exact S 17 98 1 (by decide +kernel)
 · exact S 17 98 2 (by decide +kernel)
 · exact S 17 98 3 (by decide +kernel)
 · exact S 17 98 4 (by decide +kernel)
 · exact S 17 98 5 (by decide +kernel)
theorem q17_99:ThresholdAt 17 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 99 0 (by decide +kernel)
 · exact S 17 99 1 (by decide +kernel)
 · exact S 17 99 2 (by decide +kernel)
 · exact S 17 99 3 (by decide +kernel)
 · exact S 17 99 4 (by decide +kernel)
 · exact S 17 99 5 (by decide +kernel)
theorem q17_100:ThresholdAt 17 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 100 0 (by decide +kernel)
 · exact S 17 100 1 (by decide +kernel)
 · exact S 17 100 2 (by decide +kernel)
 · exact S 17 100 3 (by decide +kernel)
 · exact S 17 100 4 (by decide +kernel)
 · exact S 17 100 5 (by decide +kernel)
theorem q17_101:ThresholdAt 17 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 101 0 (by decide +kernel)
 · exact S 17 101 1 (by decide +kernel)
 · exact S 17 101 2 (by decide +kernel)
 · exact S 17 101 3 (by decide +kernel)
 · exact S 17 101 4 (by decide +kernel)
 · exact S 17 101 5 (by decide +kernel)
theorem q17_102:ThresholdAt 17 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 102 0 (by decide +kernel)
 · exact S 17 102 1 (by decide +kernel)
 · exact S 17 102 2 (by decide +kernel)
 · exact S 17 102 3 (by decide +kernel)
 · exact S 17 102 4 (by decide +kernel)
 · exact S 17 102 5 (by decide +kernel)
theorem q17_103:ThresholdAt 17 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 103 0 (by decide +kernel)
 · exact S 17 103 1 (by decide +kernel)
 · exact S 17 103 2 (by decide +kernel)
 · exact S 17 103 3 (by decide +kernel)
 · exact S 17 103 4 (by decide +kernel)
 · exact S 17 103 5 (by decide +kernel)
theorem q17_104:ThresholdAt 17 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 104 0 (by decide +kernel)
 · exact S 17 104 1 (by decide +kernel)
 · exact S 17 104 2 (by decide +kernel)
 · exact S 17 104 3 (by decide +kernel)
 · exact S 17 104 4 (by decide +kernel)
 · exact S 17 104 5 (by decide +kernel)
theorem q17_105:ThresholdAt 17 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 105 0 (by decide +kernel)
 · exact S 17 105 1 (by decide +kernel)
 · exact S 17 105 2 (by decide +kernel)
 · exact S 17 105 3 (by decide +kernel)
 · exact S 17 105 4 (by decide +kernel)
 · exact S 17 105 5 (by decide +kernel)
theorem q17_106:ThresholdAt 17 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 106 0 (by decide +kernel)
 · exact S 17 106 1 (by decide +kernel)
 · exact S 17 106 2 (by decide +kernel)
 · exact S 17 106 3 (by decide +kernel)
 · exact S 17 106 4 (by decide +kernel)
 · exact S 17 106 5 (by decide +kernel)
theorem q17_107:ThresholdAt 17 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 107 0 (by decide +kernel)
 · exact S 17 107 1 (by decide +kernel)
 · exact S 17 107 2 (by decide +kernel)
 · exact S 17 107 3 (by decide +kernel)
 · exact S 17 107 4 (by decide +kernel)
 · exact S 17 107 5 (by decide +kernel)
theorem q17_108:ThresholdAt 17 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 108 0 (by decide +kernel)
 · exact S 17 108 1 (by decide +kernel)
 · exact S 17 108 2 (by decide +kernel)
 · exact S 17 108 3 (by decide +kernel)
 · exact S 17 108 4 (by decide +kernel)
 · exact S 17 108 5 (by decide +kernel)
theorem q17_109:ThresholdAt 17 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 109 0 (by decide +kernel)
 · exact S 17 109 1 (by decide +kernel)
 · exact S 17 109 2 (by decide +kernel)
 · exact S 17 109 3 (by decide +kernel)
 · exact S 17 109 4 (by decide +kernel)
 · exact S 17 109 5 (by decide +kernel)
theorem q17_110:ThresholdAt 17 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 110 0 (by decide +kernel)
 · exact S 17 110 1 (by decide +kernel)
 · exact S 17 110 2 (by decide +kernel)
 · exact S 17 110 3 (by decide +kernel)
 · exact S 17 110 4 (by decide +kernel)
 · exact S 17 110 5 (by decide +kernel)
theorem q17_111:ThresholdAt 17 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 111 0 (by decide +kernel)
 · exact S 17 111 1 (by decide +kernel)
 · exact S 17 111 2 (by decide +kernel)
 · exact S 17 111 3 (by decide +kernel)
 · exact S 17 111 4 (by decide +kernel)
 · exact S 17 111 5 (by decide +kernel)
theorem q17_112:ThresholdAt 17 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 112 0 (by decide +kernel)
 · exact S 17 112 1 (by decide +kernel)
 · exact S 17 112 2 (by decide +kernel)
 · exact S 17 112 3 (by decide +kernel)
 · exact S 17 112 4 (by decide +kernel)
 · exact S 17 112 5 (by decide +kernel)
theorem q17_113:ThresholdAt 17 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 113 0 (by decide +kernel)
 · exact S 17 113 1 (by decide +kernel)
 · exact S 17 113 2 (by decide +kernel)
 · exact S 17 113 3 (by decide +kernel)
 · exact S 17 113 4 (by decide +kernel)
 · exact S 17 113 5 (by decide +kernel)
theorem q17_114:ThresholdAt 17 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 114 0 (by decide +kernel)
 · exact S 17 114 1 (by decide +kernel)
 · exact S 17 114 2 (by decide +kernel)
 · exact S 17 114 3 (by decide +kernel)
 · exact S 17 114 4 (by decide +kernel)
 · exact S 17 114 5 (by decide +kernel)
theorem q17_115:ThresholdAt 17 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 115 0 (by decide +kernel)
 · exact S 17 115 1 (by decide +kernel)
 · exact S 17 115 2 (by decide +kernel)
 · exact S 17 115 3 (by decide +kernel)
 · exact S 17 115 4 (by decide +kernel)
 · exact S 17 115 5 (by decide +kernel)
theorem q17_116:ThresholdAt 17 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 116 0 (by decide +kernel)
 · exact S 17 116 1 (by decide +kernel)
 · exact S 17 116 2 (by decide +kernel)
 · exact S 17 116 3 (by decide +kernel)
 · exact S 17 116 4 (by decide +kernel)
 · exact S 17 116 5 (by decide +kernel)
theorem q17_117:ThresholdAt 17 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 117 0 (by decide +kernel)
 · exact S 17 117 1 (by decide +kernel)
 · exact S 17 117 2 (by decide +kernel)
 · exact S 17 117 3 (by decide +kernel)
 · exact S 17 117 4 (by decide +kernel)
 · exact S 17 117 5 (by decide +kernel)
theorem q17_118:ThresholdAt 17 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 118 0 (by decide +kernel)
 · exact S 17 118 1 (by decide +kernel)
 · exact S 17 118 2 (by decide +kernel)
 · exact S 17 118 3 (by decide +kernel)
 · exact S 17 118 4 (by decide +kernel)
 · exact S 17 118 5 (by decide +kernel)
theorem q17_119:ThresholdAt 17 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 119 0 (by decide +kernel)
 · exact S 17 119 1 (by decide +kernel)
 · exact S 17 119 2 (by decide +kernel)
 · exact S 17 119 3 (by decide +kernel)
 · exact S 17 119 4 (by decide +kernel)
 · exact S 17 119 5 (by decide +kernel)
theorem q17_120:ThresholdAt 17 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 120 0 (by decide +kernel)
 · exact S 17 120 1 (by decide +kernel)
 · exact S 17 120 2 (by decide +kernel)
 · exact S 17 120 3 (by decide +kernel)
 · exact S 17 120 4 (by decide +kernel)
 · exact S 17 120 5 (by decide +kernel)
theorem q17_121:ThresholdAt 17 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 121 0 (by decide +kernel)
 · exact S 17 121 1 (by decide +kernel)
 · exact S 17 121 2 (by decide +kernel)
 · exact S 17 121 3 (by decide +kernel)
 · exact S 17 121 4 (by decide +kernel)
 · exact S 17 121 5 (by decide +kernel)
theorem q17_122:ThresholdAt 17 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 122 0 (by decide +kernel)
 · exact S 17 122 1 (by decide +kernel)
 · exact S 17 122 2 (by decide +kernel)
 · exact S 17 122 3 (by decide +kernel)
 · exact S 17 122 4 (by decide +kernel)
 · exact S 17 122 5 (by decide +kernel)
theorem q17_123:ThresholdAt 17 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 123 0 (by decide +kernel)
 · exact S 17 123 1 (by decide +kernel)
 · exact S 17 123 2 (by decide +kernel)
 · exact S 17 123 3 (by decide +kernel)
 · exact S 17 123 4 (by decide +kernel)
 · exact S 17 123 5 (by decide +kernel)
theorem q17_124:ThresholdAt 17 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 124 0 (by decide +kernel)
 · exact S 17 124 1 (by decide +kernel)
 · exact S 17 124 2 (by decide +kernel)
 · exact S 17 124 3 (by decide +kernel)
 · exact S 17 124 4 (by decide +kernel)
 · exact S 17 124 5 (by decide +kernel)
theorem q17_125:ThresholdAt 17 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 17 125 0 (by decide +kernel)
 · exact S 17 125 1 (by decide +kernel)
 · exact S 17 125 2 (by decide +kernel)
 · exact S 17 125 3 (by decide +kernel)
 · exact S 17 125 4 (by decide +kernel)
 · exact S 17 125 5 (by decide +kernel)
theorem checkedR17:∀ V ∈ List.range 126,ThresholdAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0_126:V < 63
  · by_cases h0_63:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q17_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q17_1
              · have he:V = 2:=by omega
                subst V
                exact q17_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q17_3
              · have he:V = 4:=by omega
                subst V
                exact q17_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q17_5
              · have he:V = 6:=by omega
                subst V
                exact q17_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q17_7
              · have he:V = 8:=by omega
                subst V
                exact q17_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q17_9
              · have he:V = 10:=by omega
                subst V
                exact q17_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q17_11
              · have he:V = 12:=by omega
                subst V
                exact q17_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q17_13
              · have he:V = 14:=by omega
                subst V
                exact q17_14
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q17_15
              · have he:V = 16:=by omega
                subst V
                exact q17_16
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q17_17
              · have he:V = 18:=by omega
                subst V
                exact q17_18
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q17_19
              · have he:V = 20:=by omega
                subst V
                exact q17_20
            · by_cases h21_23:V < 22
              · have he:V = 21:=by omega
                subst V
                exact q17_21
              · have he:V = 22:=by omega
                subst V
                exact q17_22
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have he:V = 23:=by omega
                subst V
                exact q17_23
              · have he:V = 24:=by omega
                subst V
                exact q17_24
            · by_cases h25_27:V < 26
              · have he:V = 25:=by omega
                subst V
                exact q17_25
              · have he:V = 26:=by omega
                subst V
                exact q17_26
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have he:V = 27:=by omega
                subst V
                exact q17_27
              · have he:V = 28:=by omega
                subst V
                exact q17_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q17_29
              · have he:V = 30:=by omega
                subst V
                exact q17_30
    · by_cases h31_63:V < 47
      · by_cases h31_47:V < 39
        · by_cases h31_39:V < 35
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q17_31
              · have he:V = 32:=by omega
                subst V
                exact q17_32
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q17_33
              · have he:V = 34:=by omega
                subst V
                exact q17_34
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q17_35
              · have he:V = 36:=by omega
                subst V
                exact q17_36
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q17_37
              · have he:V = 38:=by omega
                subst V
                exact q17_38
        · by_cases h39_47:V < 43
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q17_39
              · have he:V = 40:=by omega
                subst V
                exact q17_40
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q17_41
              · have he:V = 42:=by omega
                subst V
                exact q17_42
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q17_43
              · have he:V = 44:=by omega
                subst V
                exact q17_44
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q17_45
              · have he:V = 46:=by omega
                subst V
                exact q17_46
      · by_cases h47_63:V < 55
        · by_cases h47_55:V < 51
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q17_47
              · have he:V = 48:=by omega
                subst V
                exact q17_48
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q17_49
              · have he:V = 50:=by omega
                subst V
                exact q17_50
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q17_51
              · have he:V = 52:=by omega
                subst V
                exact q17_52
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q17_53
              · have he:V = 54:=by omega
                subst V
                exact q17_54
        · by_cases h55_63:V < 59
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q17_55
              · have he:V = 56:=by omega
                subst V
                exact q17_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q17_57
              · have he:V = 58:=by omega
                subst V
                exact q17_58
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q17_59
              · have he:V = 60:=by omega
                subst V
                exact q17_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q17_61
              · have he:V = 62:=by omega
                subst V
                exact q17_62
  · by_cases h63_126:V < 94
    · by_cases h63_94:V < 78
      · by_cases h63_78:V < 70
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have he:V = 63:=by omega
              subst V
              exact q17_63
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q17_64
              · have he:V = 65:=by omega
                subst V
                exact q17_65
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q17_66
              · have he:V = 67:=by omega
                subst V
                exact q17_67
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q17_68
              · have he:V = 69:=by omega
                subst V
                exact q17_69
        · by_cases h70_78:V < 74
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q17_70
              · have he:V = 71:=by omega
                subst V
                exact q17_71
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q17_72
              · have he:V = 73:=by omega
                subst V
                exact q17_73
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q17_74
              · have he:V = 75:=by omega
                subst V
                exact q17_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q17_76
              · have he:V = 77:=by omega
                subst V
                exact q17_77
      · by_cases h78_94:V < 86
        · by_cases h78_86:V < 82
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q17_78
              · have he:V = 79:=by omega
                subst V
                exact q17_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q17_80
              · have he:V = 81:=by omega
                subst V
                exact q17_81
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q17_82
              · have he:V = 83:=by omega
                subst V
                exact q17_83
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q17_84
              · have he:V = 85:=by omega
                subst V
                exact q17_85
        · by_cases h86_94:V < 90
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q17_86
              · have he:V = 87:=by omega
                subst V
                exact q17_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q17_88
              · have he:V = 89:=by omega
                subst V
                exact q17_89
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q17_90
              · have he:V = 91:=by omega
                subst V
                exact q17_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q17_92
              · have he:V = 93:=by omega
                subst V
                exact q17_93
    · by_cases h94_126:V < 110
      · by_cases h94_110:V < 102
        · by_cases h94_102:V < 98
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q17_94
              · have he:V = 95:=by omega
                subst V
                exact q17_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q17_96
              · have he:V = 97:=by omega
                subst V
                exact q17_97
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have he:V = 98:=by omega
                subst V
                exact q17_98
              · have he:V = 99:=by omega
                subst V
                exact q17_99
            · by_cases h100_102:V < 101
              · have he:V = 100:=by omega
                subst V
                exact q17_100
              · have he:V = 101:=by omega
                subst V
                exact q17_101
        · by_cases h102_110:V < 106
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have he:V = 102:=by omega
                subst V
                exact q17_102
              · have he:V = 103:=by omega
                subst V
                exact q17_103
            · by_cases h104_106:V < 105
              · have he:V = 104:=by omega
                subst V
                exact q17_104
              · have he:V = 105:=by omega
                subst V
                exact q17_105
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q17_106
              · have he:V = 107:=by omega
                subst V
                exact q17_107
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q17_108
              · have he:V = 109:=by omega
                subst V
                exact q17_109
      · by_cases h110_126:V < 118
        · by_cases h110_118:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q17_110
              · have he:V = 111:=by omega
                subst V
                exact q17_111
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q17_112
              · have he:V = 113:=by omega
                subst V
                exact q17_113
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q17_114
              · have he:V = 115:=by omega
                subst V
                exact q17_115
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q17_116
              · have he:V = 117:=by omega
                subst V
                exact q17_117
        · by_cases h118_126:V < 122
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q17_118
              · have he:V = 119:=by omega
                subst V
                exact q17_119
            · by_cases h120_122:V < 121
              · have he:V = 120:=by omega
                subst V
                exact q17_120
              · have he:V = 121:=by omega
                subst V
                exact q17_121
          · by_cases h122_126:V < 124
            · by_cases h122_124:V < 123
              · have he:V = 122:=by omega
                subst V
                exact q17_122
              · have he:V = 123:=by omega
                subst V
                exact q17_123
            · by_cases h124_126:V < 125
              · have he:V = 124:=by omega
                subst V
                exact q17_124
              · have he:V = 125:=by omega
                subst V
                exact q17_125
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
