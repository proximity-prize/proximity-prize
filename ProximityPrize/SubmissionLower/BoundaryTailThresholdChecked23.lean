import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked22

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q23_0:ThresholdAt 23 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 0 0 (by decide +kernel)
 · exact S 23 0 1 (by decide +kernel)
 · exact S 23 0 2 (by decide +kernel)
 · exact S 23 0 3 (by decide +kernel)
 · exact S 23 0 4 (by decide +kernel)
 · exact S 23 0 5 (by decide +kernel)
theorem q23_1:ThresholdAt 23 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 1 0 (by decide +kernel)
 · exact S 23 1 1 (by decide +kernel)
 · exact S 23 1 2 (by decide +kernel)
 · exact S 23 1 3 (by decide +kernel)
 · exact S 23 1 4 (by decide +kernel)
 · exact S 23 1 5 (by decide +kernel)
theorem q23_2:ThresholdAt 23 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 2 0 (by decide +kernel)
 · exact S 23 2 1 (by decide +kernel)
 · exact S 23 2 2 (by decide +kernel)
 · exact S 23 2 3 (by decide +kernel)
 · exact S 23 2 4 (by decide +kernel)
 · exact S 23 2 5 (by decide +kernel)
theorem q23_3:ThresholdAt 23 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 3 0 (by decide +kernel)
 · exact S 23 3 1 (by decide +kernel)
 · exact S 23 3 2 (by decide +kernel)
 · exact S 23 3 3 (by decide +kernel)
 · exact S 23 3 4 (by decide +kernel)
 · exact S 23 3 5 (by decide +kernel)
theorem q23_4:ThresholdAt 23 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 4 0 (by decide +kernel)
 · exact S 23 4 1 (by decide +kernel)
 · exact S 23 4 2 (by decide +kernel)
 · exact S 23 4 3 (by decide +kernel)
 · exact S 23 4 4 (by decide +kernel)
 · exact S 23 4 5 (by decide +kernel)
theorem q23_5:ThresholdAt 23 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 5 0 (by decide +kernel)
 · exact S 23 5 1 (by decide +kernel)
 · exact S 23 5 2 (by decide +kernel)
 · exact S 23 5 3 (by decide +kernel)
 · exact S 23 5 4 (by decide +kernel)
 · exact S 23 5 5 (by decide +kernel)
theorem q23_6:ThresholdAt 23 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 6 0 (by decide +kernel)
 · exact S 23 6 1 (by decide +kernel)
 · exact S 23 6 2 (by decide +kernel)
 · exact S 23 6 3 (by decide +kernel)
 · exact S 23 6 4 (by decide +kernel)
 · exact S 23 6 5 (by decide +kernel)
theorem q23_7:ThresholdAt 23 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 7 0 (by decide +kernel)
 · exact S 23 7 1 (by decide +kernel)
 · exact S 23 7 2 (by decide +kernel)
 · exact S 23 7 3 (by decide +kernel)
 · exact S 23 7 4 (by decide +kernel)
 · exact S 23 7 5 (by decide +kernel)
theorem q23_8:ThresholdAt 23 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 8 0 (by decide +kernel)
 · exact S 23 8 1 (by decide +kernel)
 · exact S 23 8 2 (by decide +kernel)
 · exact S 23 8 3 (by decide +kernel)
 · exact S 23 8 4 (by decide +kernel)
 · exact S 23 8 5 (by decide +kernel)
theorem q23_9:ThresholdAt 23 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 9 0 (by decide +kernel)
 · exact S 23 9 1 (by decide +kernel)
 · exact S 23 9 2 (by decide +kernel)
 · exact S 23 9 3 (by decide +kernel)
 · exact S 23 9 4 (by decide +kernel)
 · exact S 23 9 5 (by decide +kernel)
theorem q23_10:ThresholdAt 23 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 10 0 (by decide +kernel)
 · exact S 23 10 1 (by decide +kernel)
 · exact S 23 10 2 (by decide +kernel)
 · exact S 23 10 3 (by decide +kernel)
 · exact S 23 10 4 (by decide +kernel)
 · exact S 23 10 5 (by decide +kernel)
theorem q23_11:ThresholdAt 23 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 11 0 (by decide +kernel)
 · exact S 23 11 1 (by decide +kernel)
 · exact S 23 11 2 (by decide +kernel)
 · exact S 23 11 3 (by decide +kernel)
 · exact S 23 11 4 (by decide +kernel)
 · exact S 23 11 5 (by decide +kernel)
theorem q23_12:ThresholdAt 23 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 12 0 (by decide +kernel)
 · exact S 23 12 1 (by decide +kernel)
 · exact S 23 12 2 (by decide +kernel)
 · exact S 23 12 3 (by decide +kernel)
 · exact S 23 12 4 (by decide +kernel)
 · exact S 23 12 5 (by decide +kernel)
theorem q23_13:ThresholdAt 23 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 13 0 (by decide +kernel)
 · exact S 23 13 1 (by decide +kernel)
 · exact S 23 13 2 (by decide +kernel)
 · exact S 23 13 3 (by decide +kernel)
 · exact S 23 13 4 (by decide +kernel)
 · exact S 23 13 5 (by decide +kernel)
theorem q23_14:ThresholdAt 23 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 14 0 (by decide +kernel)
 · exact S 23 14 1 (by decide +kernel)
 · exact S 23 14 2 (by decide +kernel)
 · exact S 23 14 3 (by decide +kernel)
 · exact S 23 14 4 (by decide +kernel)
 · exact S 23 14 5 (by decide +kernel)
theorem q23_15:ThresholdAt 23 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 15 0 (by decide +kernel)
 · exact S 23 15 1 (by decide +kernel)
 · exact S 23 15 2 (by decide +kernel)
 · exact S 23 15 3 (by decide +kernel)
 · exact S 23 15 4 (by decide +kernel)
 · exact S 23 15 5 (by decide +kernel)
theorem q23_16:ThresholdAt 23 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 16 0 (by decide +kernel)
 · exact S 23 16 1 (by decide +kernel)
 · exact S 23 16 2 (by decide +kernel)
 · exact S 23 16 3 (by decide +kernel)
 · exact S 23 16 4 (by decide +kernel)
 · exact S 23 16 5 (by decide +kernel)
theorem q23_17:ThresholdAt 23 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 17 0 (by decide +kernel)
 · exact S 23 17 1 (by decide +kernel)
 · exact S 23 17 2 (by decide +kernel)
 · exact S 23 17 3 (by decide +kernel)
 · exact S 23 17 4 (by decide +kernel)
 · exact S 23 17 5 (by decide +kernel)
theorem q23_18:ThresholdAt 23 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 18 0 (by decide +kernel)
 · exact S 23 18 1 (by decide +kernel)
 · exact S 23 18 2 (by decide +kernel)
 · exact S 23 18 3 (by decide +kernel)
 · exact S 23 18 4 (by decide +kernel)
 · exact S 23 18 5 (by decide +kernel)
theorem q23_19:ThresholdAt 23 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 19 0 (by decide +kernel)
 · exact S 23 19 1 (by decide +kernel)
 · exact S 23 19 2 (by decide +kernel)
 · exact S 23 19 3 (by decide +kernel)
 · exact S 23 19 4 (by decide +kernel)
 · exact S 23 19 5 (by decide +kernel)
theorem q23_20:ThresholdAt 23 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 20 0 (by decide +kernel)
 · exact S 23 20 1 (by decide +kernel)
 · exact S 23 20 2 (by decide +kernel)
 · exact S 23 20 3 (by decide +kernel)
 · exact S 23 20 4 (by decide +kernel)
 · exact S 23 20 5 (by decide +kernel)
theorem q23_21:ThresholdAt 23 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 21 0 (by decide +kernel)
 · exact S 23 21 1 (by decide +kernel)
 · exact S 23 21 2 (by decide +kernel)
 · exact S 23 21 3 (by decide +kernel)
 · exact S 23 21 4 (by decide +kernel)
 · exact S 23 21 5 (by decide +kernel)
theorem q23_22:ThresholdAt 23 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 22 0 (by decide +kernel)
 · exact S 23 22 1 (by decide +kernel)
 · exact S 23 22 2 (by decide +kernel)
 · exact S 23 22 3 (by decide +kernel)
 · exact S 23 22 4 (by decide +kernel)
 · exact S 23 22 5 (by decide +kernel)
theorem q23_23:ThresholdAt 23 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 23 0 (by decide +kernel)
 · exact S 23 23 1 (by decide +kernel)
 · exact S 23 23 2 (by decide +kernel)
 · exact S 23 23 3 (by decide +kernel)
 · exact S 23 23 4 (by decide +kernel)
 · exact S 23 23 5 (by decide +kernel)
theorem q23_24:ThresholdAt 23 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 24 0 (by decide +kernel)
 · exact S 23 24 1 (by decide +kernel)
 · exact S 23 24 2 (by decide +kernel)
 · exact S 23 24 3 (by decide +kernel)
 · exact S 23 24 4 (by decide +kernel)
 · exact S 23 24 5 (by decide +kernel)
theorem q23_25:ThresholdAt 23 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 25 0 (by decide +kernel)
 · exact S 23 25 1 (by decide +kernel)
 · exact S 23 25 2 (by decide +kernel)
 · exact S 23 25 3 (by decide +kernel)
 · exact S 23 25 4 (by decide +kernel)
 · exact S 23 25 5 (by decide +kernel)
theorem q23_26:ThresholdAt 23 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 26 0 (by decide +kernel)
 · exact S 23 26 1 (by decide +kernel)
 · exact S 23 26 2 (by decide +kernel)
 · exact S 23 26 3 (by decide +kernel)
 · exact S 23 26 4 (by decide +kernel)
 · exact S 23 26 5 (by decide +kernel)
theorem q23_27:ThresholdAt 23 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 27 0 (by decide +kernel)
 · exact S 23 27 1 (by decide +kernel)
 · exact S 23 27 2 (by decide +kernel)
 · exact S 23 27 3 (by decide +kernel)
 · exact S 23 27 4 (by decide +kernel)
 · exact S 23 27 5 (by decide +kernel)
theorem q23_28:ThresholdAt 23 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 28 0 (by decide +kernel)
 · exact S 23 28 1 (by decide +kernel)
 · exact S 23 28 2 (by decide +kernel)
 · exact S 23 28 3 (by decide +kernel)
 · exact S 23 28 4 (by decide +kernel)
 · exact S 23 28 5 (by decide +kernel)
theorem q23_29:ThresholdAt 23 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 29 0 (by decide +kernel)
 · exact S 23 29 1 (by decide +kernel)
 · exact S 23 29 2 (by decide +kernel)
 · exact S 23 29 3 (by decide +kernel)
 · exact S 23 29 4 (by decide +kernel)
 · exact S 23 29 5 (by decide +kernel)
theorem q23_30:ThresholdAt 23 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 30 0 (by decide +kernel)
 · exact S 23 30 1 (by decide +kernel)
 · exact S 23 30 2 (by decide +kernel)
 · exact S 23 30 3 (by decide +kernel)
 · exact S 23 30 4 (by decide +kernel)
 · exact S 23 30 5 (by decide +kernel)
theorem q23_31:ThresholdAt 23 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 31 0 (by decide +kernel)
 · exact S 23 31 1 (by decide +kernel)
 · exact S 23 31 2 (by decide +kernel)
 · exact S 23 31 3 (by decide +kernel)
 · exact S 23 31 4 (by decide +kernel)
 · exact S 23 31 5 (by decide +kernel)
theorem q23_32:ThresholdAt 23 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 32 0 (by decide +kernel)
 · exact S 23 32 1 (by decide +kernel)
 · exact S 23 32 2 (by decide +kernel)
 · exact S 23 32 3 (by decide +kernel)
 · exact S 23 32 4 (by decide +kernel)
 · exact S 23 32 5 (by decide +kernel)
theorem q23_33:ThresholdAt 23 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 33 0 (by decide +kernel)
 · exact S 23 33 1 (by decide +kernel)
 · exact S 23 33 2 (by decide +kernel)
 · exact S 23 33 3 (by decide +kernel)
 · exact S 23 33 4 (by decide +kernel)
 · exact S 23 33 5 (by decide +kernel)
theorem q23_34:ThresholdAt 23 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 34 0 (by decide +kernel)
 · exact S 23 34 1 (by decide +kernel)
 · exact S 23 34 2 (by decide +kernel)
 · exact S 23 34 3 (by decide +kernel)
 · exact S 23 34 4 (by decide +kernel)
 · exact S 23 34 5 (by decide +kernel)
theorem q23_35:ThresholdAt 23 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 35 0 (by decide +kernel)
 · exact S 23 35 1 (by decide +kernel)
 · exact S 23 35 2 (by decide +kernel)
 · exact S 23 35 3 (by decide +kernel)
 · exact S 23 35 4 (by decide +kernel)
 · exact S 23 35 5 (by decide +kernel)
theorem q23_36:ThresholdAt 23 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 36 0 (by decide +kernel)
 · exact S 23 36 1 (by decide +kernel)
 · exact S 23 36 2 (by decide +kernel)
 · exact S 23 36 3 (by decide +kernel)
 · exact S 23 36 4 (by decide +kernel)
 · exact S 23 36 5 (by decide +kernel)
theorem q23_37:ThresholdAt 23 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 37 0 (by decide +kernel)
 · exact S 23 37 1 (by decide +kernel)
 · exact S 23 37 2 (by decide +kernel)
 · exact S 23 37 3 (by decide +kernel)
 · exact S 23 37 4 (by decide +kernel)
 · exact S 23 37 5 (by decide +kernel)
theorem q23_38:ThresholdAt 23 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 38 0 (by decide +kernel)
 · exact S 23 38 1 (by decide +kernel)
 · exact S 23 38 2 (by decide +kernel)
 · exact S 23 38 3 (by decide +kernel)
 · exact S 23 38 4 (by decide +kernel)
 · exact S 23 38 5 (by decide +kernel)
theorem q23_39:ThresholdAt 23 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 39 0 (by decide +kernel)
 · exact S 23 39 1 (by decide +kernel)
 · exact S 23 39 2 (by decide +kernel)
 · exact S 23 39 3 (by decide +kernel)
 · exact S 23 39 4 (by decide +kernel)
 · exact S 23 39 5 (by decide +kernel)
theorem q23_40:ThresholdAt 23 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 40 0 (by decide +kernel)
 · exact S 23 40 1 (by decide +kernel)
 · exact S 23 40 2 (by decide +kernel)
 · exact S 23 40 3 (by decide +kernel)
 · exact S 23 40 4 (by decide +kernel)
 · exact S 23 40 5 (by decide +kernel)
theorem q23_41:ThresholdAt 23 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 41 0 (by decide +kernel)
 · exact S 23 41 1 (by decide +kernel)
 · exact S 23 41 2 (by decide +kernel)
 · exact S 23 41 3 (by decide +kernel)
 · exact S 23 41 4 (by decide +kernel)
 · exact S 23 41 5 (by decide +kernel)
theorem q23_42:ThresholdAt 23 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 42 0 (by decide +kernel)
 · exact S 23 42 1 (by decide +kernel)
 · exact S 23 42 2 (by decide +kernel)
 · exact S 23 42 3 (by decide +kernel)
 · exact S 23 42 4 (by decide +kernel)
 · exact S 23 42 5 (by decide +kernel)
theorem q23_43:ThresholdAt 23 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 43 0 (by decide +kernel)
 · exact S 23 43 1 (by decide +kernel)
 · exact S 23 43 2 (by decide +kernel)
 · exact S 23 43 3 (by decide +kernel)
 · exact S 23 43 4 (by decide +kernel)
 · exact S 23 43 5 (by decide +kernel)
theorem q23_44:ThresholdAt 23 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 44 0 (by decide +kernel)
 · exact S 23 44 1 (by decide +kernel)
 · exact S 23 44 2 (by decide +kernel)
 · exact S 23 44 3 (by decide +kernel)
 · exact S 23 44 4 (by decide +kernel)
 · exact S 23 44 5 (by decide +kernel)
theorem q23_45:ThresholdAt 23 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 45 0 (by decide +kernel)
 · exact S 23 45 1 (by decide +kernel)
 · exact S 23 45 2 (by decide +kernel)
 · exact S 23 45 3 (by decide +kernel)
 · exact S 23 45 4 (by decide +kernel)
 · exact S 23 45 5 (by decide +kernel)
theorem q23_46:ThresholdAt 23 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 46 0 (by decide +kernel)
 · exact S 23 46 1 (by decide +kernel)
 · exact S 23 46 2 (by decide +kernel)
 · exact S 23 46 3 (by decide +kernel)
 · exact S 23 46 4 (by decide +kernel)
 · exact S 23 46 5 (by decide +kernel)
theorem q23_47:ThresholdAt 23 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 47 0 (by decide +kernel)
 · exact S 23 47 1 (by decide +kernel)
 · exact S 23 47 2 (by decide +kernel)
 · exact S 23 47 3 (by decide +kernel)
 · exact S 23 47 4 (by decide +kernel)
 · exact S 23 47 5 (by decide +kernel)
theorem q23_48:ThresholdAt 23 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 48 0 (by decide +kernel)
 · exact S 23 48 1 (by decide +kernel)
 · exact S 23 48 2 (by decide +kernel)
 · exact S 23 48 3 (by decide +kernel)
 · exact S 23 48 4 (by decide +kernel)
 · exact S 23 48 5 (by decide +kernel)
theorem q23_49:ThresholdAt 23 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 49 0 (by decide +kernel)
 · exact S 23 49 1 (by decide +kernel)
 · exact S 23 49 2 (by decide +kernel)
 · exact S 23 49 3 (by decide +kernel)
 · exact S 23 49 4 (by decide +kernel)
 · exact S 23 49 5 (by decide +kernel)
theorem q23_50:ThresholdAt 23 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 50 0 (by decide +kernel)
 · exact S 23 50 1 (by decide +kernel)
 · exact S 23 50 2 (by decide +kernel)
 · exact S 23 50 3 (by decide +kernel)
 · exact S 23 50 4 (by decide +kernel)
 · exact S 23 50 5 (by decide +kernel)
theorem q23_51:ThresholdAt 23 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 51 0 (by decide +kernel)
 · exact S 23 51 1 (by decide +kernel)
 · exact S 23 51 2 (by decide +kernel)
 · exact S 23 51 3 (by decide +kernel)
 · exact S 23 51 4 (by decide +kernel)
 · exact S 23 51 5 (by decide +kernel)
theorem q23_52:ThresholdAt 23 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 52 0 (by decide +kernel)
 · exact S 23 52 1 (by decide +kernel)
 · exact S 23 52 2 (by decide +kernel)
 · exact S 23 52 3 (by decide +kernel)
 · exact S 23 52 4 (by decide +kernel)
 · exact S 23 52 5 (by decide +kernel)
theorem q23_53:ThresholdAt 23 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 53 0 (by decide +kernel)
 · exact S 23 53 1 (by decide +kernel)
 · exact S 23 53 2 (by decide +kernel)
 · exact S 23 53 3 (by decide +kernel)
 · exact S 23 53 4 (by decide +kernel)
 · exact S 23 53 5 (by decide +kernel)
theorem q23_54:ThresholdAt 23 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 54 0 (by decide +kernel)
 · exact S 23 54 1 (by decide +kernel)
 · exact S 23 54 2 (by decide +kernel)
 · exact S 23 54 3 (by decide +kernel)
 · exact S 23 54 4 (by decide +kernel)
 · exact S 23 54 5 (by decide +kernel)
theorem q23_55:ThresholdAt 23 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 55 0 (by decide +kernel)
 · exact S 23 55 1 (by decide +kernel)
 · exact S 23 55 2 (by decide +kernel)
 · exact S 23 55 3 (by decide +kernel)
 · exact S 23 55 4 (by decide +kernel)
 · exact S 23 55 5 (by decide +kernel)
theorem q23_56:ThresholdAt 23 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 56 0 (by decide +kernel)
 · exact S 23 56 1 (by decide +kernel)
 · exact S 23 56 2 (by decide +kernel)
 · exact S 23 56 3 (by decide +kernel)
 · exact S 23 56 4 (by decide +kernel)
 · exact S 23 56 5 (by decide +kernel)
theorem q23_57:ThresholdAt 23 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 57 0 (by decide +kernel)
 · exact S 23 57 1 (by decide +kernel)
 · exact S 23 57 2 (by decide +kernel)
 · exact S 23 57 3 (by decide +kernel)
 · exact S 23 57 4 (by decide +kernel)
 · exact S 23 57 5 (by decide +kernel)
theorem q23_58:ThresholdAt 23 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 58 0 (by decide +kernel)
 · exact S 23 58 1 (by decide +kernel)
 · exact S 23 58 2 (by decide +kernel)
 · exact S 23 58 3 (by decide +kernel)
 · exact S 23 58 4 (by decide +kernel)
 · exact S 23 58 5 (by decide +kernel)
theorem q23_59:ThresholdAt 23 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 59 0 (by decide +kernel)
 · exact S 23 59 1 (by decide +kernel)
 · exact S 23 59 2 (by decide +kernel)
 · exact S 23 59 3 (by decide +kernel)
 · exact S 23 59 4 (by decide +kernel)
 · exact S 23 59 5 (by decide +kernel)
theorem q23_60:ThresholdAt 23 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 60 0 (by decide +kernel)
 · exact S 23 60 1 (by decide +kernel)
 · exact S 23 60 2 (by decide +kernel)
 · exact S 23 60 3 (by decide +kernel)
 · exact S 23 60 4 (by decide +kernel)
 · exact S 23 60 5 (by decide +kernel)
theorem q23_61:ThresholdAt 23 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 61 0 (by decide +kernel)
 · exact S 23 61 1 (by decide +kernel)
 · exact S 23 61 2 (by decide +kernel)
 · exact S 23 61 3 (by decide +kernel)
 · exact S 23 61 4 (by decide +kernel)
 · exact S 23 61 5 (by decide +kernel)
theorem q23_62:ThresholdAt 23 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 62 0 (by decide +kernel)
 · exact S 23 62 1 (by decide +kernel)
 · exact S 23 62 2 (by decide +kernel)
 · exact S 23 62 3 (by decide +kernel)
 · exact S 23 62 4 (by decide +kernel)
 · exact S 23 62 5 (by decide +kernel)
theorem q23_63:ThresholdAt 23 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 63 0 (by decide +kernel)
 · exact S 23 63 1 (by decide +kernel)
 · exact S 23 63 2 (by decide +kernel)
 · exact S 23 63 3 (by decide +kernel)
 · exact S 23 63 4 (by decide +kernel)
 · exact S 23 63 5 (by decide +kernel)
theorem q23_64:ThresholdAt 23 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 64 0 (by decide +kernel)
 · exact S 23 64 1 (by decide +kernel)
 · exact S 23 64 2 (by decide +kernel)
 · exact S 23 64 3 (by decide +kernel)
 · exact S 23 64 4 (by decide +kernel)
 · exact S 23 64 5 (by decide +kernel)
theorem q23_65:ThresholdAt 23 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 65 0 (by decide +kernel)
 · exact S 23 65 1 (by decide +kernel)
 · exact S 23 65 2 (by decide +kernel)
 · exact S 23 65 3 (by decide +kernel)
 · exact S 23 65 4 (by decide +kernel)
 · exact S 23 65 5 (by decide +kernel)
theorem q23_66:ThresholdAt 23 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 66 0 (by decide +kernel)
 · exact S 23 66 1 (by decide +kernel)
 · exact S 23 66 2 (by decide +kernel)
 · exact S 23 66 3 (by decide +kernel)
 · exact S 23 66 4 (by decide +kernel)
 · exact S 23 66 5 (by decide +kernel)
theorem q23_67:ThresholdAt 23 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 67 0 (by decide +kernel)
 · exact S 23 67 1 (by decide +kernel)
 · exact S 23 67 2 (by decide +kernel)
 · exact S 23 67 3 (by decide +kernel)
 · exact S 23 67 4 (by decide +kernel)
 · exact S 23 67 5 (by decide +kernel)
theorem q23_68:ThresholdAt 23 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 68 0 (by decide +kernel)
 · exact S 23 68 1 (by decide +kernel)
 · exact S 23 68 2 (by decide +kernel)
 · exact S 23 68 3 (by decide +kernel)
 · exact S 23 68 4 (by decide +kernel)
 · exact S 23 68 5 (by decide +kernel)
theorem q23_69:ThresholdAt 23 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 69 0 (by decide +kernel)
 · exact S 23 69 1 (by decide +kernel)
 · exact S 23 69 2 (by decide +kernel)
 · exact S 23 69 3 (by decide +kernel)
 · exact S 23 69 4 (by decide +kernel)
 · exact S 23 69 5 (by decide +kernel)
theorem q23_70:ThresholdAt 23 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 70 0 (by decide +kernel)
 · exact S 23 70 1 (by decide +kernel)
 · exact S 23 70 2 (by decide +kernel)
 · exact S 23 70 3 (by decide +kernel)
 · exact S 23 70 4 (by decide +kernel)
 · exact S 23 70 5 (by decide +kernel)
theorem q23_71:ThresholdAt 23 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 71 0 (by decide +kernel)
 · exact S 23 71 1 (by decide +kernel)
 · exact S 23 71 2 (by decide +kernel)
 · exact S 23 71 3 (by decide +kernel)
 · exact S 23 71 4 (by decide +kernel)
 · exact S 23 71 5 (by decide +kernel)
theorem q23_72:ThresholdAt 23 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 72 0 (by decide +kernel)
 · exact S 23 72 1 (by decide +kernel)
 · exact S 23 72 2 (by decide +kernel)
 · exact S 23 72 3 (by decide +kernel)
 · exact S 23 72 4 (by decide +kernel)
 · exact S 23 72 5 (by decide +kernel)
theorem q23_73:ThresholdAt 23 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 73 0 (by decide +kernel)
 · exact S 23 73 1 (by decide +kernel)
 · exact S 23 73 2 (by decide +kernel)
 · exact S 23 73 3 (by decide +kernel)
 · exact S 23 73 4 (by decide +kernel)
 · exact S 23 73 5 (by decide +kernel)
theorem q23_74:ThresholdAt 23 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 74 0 (by decide +kernel)
 · exact S 23 74 1 (by decide +kernel)
 · exact S 23 74 2 (by decide +kernel)
 · exact S 23 74 3 (by decide +kernel)
 · exact S 23 74 4 (by decide +kernel)
 · exact S 23 74 5 (by decide +kernel)
theorem q23_75:ThresholdAt 23 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 75 0 (by decide +kernel)
 · exact S 23 75 1 (by decide +kernel)
 · exact S 23 75 2 (by decide +kernel)
 · exact S 23 75 3 (by decide +kernel)
 · exact S 23 75 4 (by decide +kernel)
 · exact S 23 75 5 (by decide +kernel)
theorem q23_76:ThresholdAt 23 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 76 0 (by decide +kernel)
 · exact S 23 76 1 (by decide +kernel)
 · exact S 23 76 2 (by decide +kernel)
 · exact S 23 76 3 (by decide +kernel)
 · exact S 23 76 4 (by decide +kernel)
 · exact S 23 76 5 (by decide +kernel)
theorem q23_77:ThresholdAt 23 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 77 0 (by decide +kernel)
 · exact S 23 77 1 (by decide +kernel)
 · exact S 23 77 2 (by decide +kernel)
 · exact S 23 77 3 (by decide +kernel)
 · exact S 23 77 4 (by decide +kernel)
 · exact S 23 77 5 (by decide +kernel)
theorem q23_78:ThresholdAt 23 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 78 0 (by decide +kernel)
 · exact S 23 78 1 (by decide +kernel)
 · exact S 23 78 2 (by decide +kernel)
 · exact S 23 78 3 (by decide +kernel)
 · exact S 23 78 4 (by decide +kernel)
 · exact S 23 78 5 (by decide +kernel)
theorem q23_79:ThresholdAt 23 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 79 0 (by decide +kernel)
 · exact S 23 79 1 (by decide +kernel)
 · exact S 23 79 2 (by decide +kernel)
 · exact S 23 79 3 (by decide +kernel)
 · exact S 23 79 4 (by decide +kernel)
 · exact S 23 79 5 (by decide +kernel)
theorem q23_80:ThresholdAt 23 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 80 0 (by decide +kernel)
 · exact S 23 80 1 (by decide +kernel)
 · exact S 23 80 2 (by decide +kernel)
 · exact S 23 80 3 (by decide +kernel)
 · exact S 23 80 4 (by decide +kernel)
 · exact S 23 80 5 (by decide +kernel)
theorem q23_81:ThresholdAt 23 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 81 0 (by decide +kernel)
 · exact S 23 81 1 (by decide +kernel)
 · exact S 23 81 2 (by decide +kernel)
 · exact S 23 81 3 (by decide +kernel)
 · exact S 23 81 4 (by decide +kernel)
 · exact S 23 81 5 (by decide +kernel)
theorem q23_82:ThresholdAt 23 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 82 0 (by decide +kernel)
 · exact S 23 82 1 (by decide +kernel)
 · exact S 23 82 2 (by decide +kernel)
 · exact S 23 82 3 (by decide +kernel)
 · exact S 23 82 4 (by decide +kernel)
 · exact S 23 82 5 (by decide +kernel)
theorem q23_83:ThresholdAt 23 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 83 0 (by decide +kernel)
 · exact S 23 83 1 (by decide +kernel)
 · exact S 23 83 2 (by decide +kernel)
 · exact S 23 83 3 (by decide +kernel)
 · exact S 23 83 4 (by decide +kernel)
 · exact S 23 83 5 (by decide +kernel)
theorem q23_84:ThresholdAt 23 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 84 0 (by decide +kernel)
 · exact S 23 84 1 (by decide +kernel)
 · exact S 23 84 2 (by decide +kernel)
 · exact S 23 84 3 (by decide +kernel)
 · exact S 23 84 4 (by decide +kernel)
 · exact S 23 84 5 (by decide +kernel)
theorem q23_85:ThresholdAt 23 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 85 0 (by decide +kernel)
 · exact S 23 85 1 (by decide +kernel)
 · exact S 23 85 2 (by decide +kernel)
 · exact S 23 85 3 (by decide +kernel)
 · exact S 23 85 4 (by decide +kernel)
 · exact S 23 85 5 (by decide +kernel)
theorem q23_86:ThresholdAt 23 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 86 0 (by decide +kernel)
 · exact S 23 86 1 (by decide +kernel)
 · exact S 23 86 2 (by decide +kernel)
 · exact S 23 86 3 (by decide +kernel)
 · exact S 23 86 4 (by decide +kernel)
 · exact S 23 86 5 (by decide +kernel)
theorem q23_87:ThresholdAt 23 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 87 0 (by decide +kernel)
 · exact S 23 87 1 (by decide +kernel)
 · exact S 23 87 2 (by decide +kernel)
 · exact S 23 87 3 (by decide +kernel)
 · exact S 23 87 4 (by decide +kernel)
 · exact S 23 87 5 (by decide +kernel)
theorem q23_88:ThresholdAt 23 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 88 0 (by decide +kernel)
 · exact S 23 88 1 (by decide +kernel)
 · exact S 23 88 2 (by decide +kernel)
 · exact S 23 88 3 (by decide +kernel)
 · exact S 23 88 4 (by decide +kernel)
 · exact S 23 88 5 (by decide +kernel)
theorem q23_89:ThresholdAt 23 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 89 0 (by decide +kernel)
 · exact S 23 89 1 (by decide +kernel)
 · exact S 23 89 2 (by decide +kernel)
 · exact S 23 89 3 (by decide +kernel)
 · exact S 23 89 4 (by decide +kernel)
 · exact S 23 89 5 (by decide +kernel)
theorem q23_90:ThresholdAt 23 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 90 0 (by decide +kernel)
 · exact S 23 90 1 (by decide +kernel)
 · exact S 23 90 2 (by decide +kernel)
 · exact S 23 90 3 (by decide +kernel)
 · exact S 23 90 4 (by decide +kernel)
 · exact S 23 90 5 (by decide +kernel)
theorem q23_91:ThresholdAt 23 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 91 0 (by decide +kernel)
 · exact S 23 91 1 (by decide +kernel)
 · exact S 23 91 2 (by decide +kernel)
 · exact S 23 91 3 (by decide +kernel)
 · exact S 23 91 4 (by decide +kernel)
 · exact S 23 91 5 (by decide +kernel)
theorem q23_92:ThresholdAt 23 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 92 0 (by decide +kernel)
 · exact S 23 92 1 (by decide +kernel)
 · exact S 23 92 2 (by decide +kernel)
 · exact S 23 92 3 (by decide +kernel)
 · exact S 23 92 4 (by decide +kernel)
 · exact S 23 92 5 (by decide +kernel)
theorem q23_93:ThresholdAt 23 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 93 0 (by decide +kernel)
 · exact S 23 93 1 (by decide +kernel)
 · exact S 23 93 2 (by decide +kernel)
 · exact S 23 93 3 (by decide +kernel)
 · exact S 23 93 4 (by decide +kernel)
 · exact S 23 93 5 (by decide +kernel)
theorem q23_94:ThresholdAt 23 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 94 0 (by decide +kernel)
 · exact S 23 94 1 (by decide +kernel)
 · exact S 23 94 2 (by decide +kernel)
 · exact S 23 94 3 (by decide +kernel)
 · exact S 23 94 4 (by decide +kernel)
 · exact S 23 94 5 (by decide +kernel)
theorem q23_95:ThresholdAt 23 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 95 0 (by decide +kernel)
 · exact S 23 95 1 (by decide +kernel)
 · exact S 23 95 2 (by decide +kernel)
 · exact S 23 95 3 (by decide +kernel)
 · exact S 23 95 4 (by decide +kernel)
 · exact S 23 95 5 (by decide +kernel)
theorem q23_96:ThresholdAt 23 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 96 0 (by decide +kernel)
 · exact S 23 96 1 (by decide +kernel)
 · exact S 23 96 2 (by decide +kernel)
 · exact S 23 96 3 (by decide +kernel)
 · exact S 23 96 4 (by decide +kernel)
 · exact S 23 96 5 (by decide +kernel)
theorem q23_97:ThresholdAt 23 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 97 0 (by decide +kernel)
 · exact S 23 97 1 (by decide +kernel)
 · exact S 23 97 2 (by decide +kernel)
 · exact S 23 97 3 (by decide +kernel)
 · exact S 23 97 4 (by decide +kernel)
 · exact S 23 97 5 (by decide +kernel)
theorem q23_98:ThresholdAt 23 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 98 0 (by decide +kernel)
 · exact S 23 98 1 (by decide +kernel)
 · exact S 23 98 2 (by decide +kernel)
 · exact S 23 98 3 (by decide +kernel)
 · exact S 23 98 4 (by decide +kernel)
 · exact S 23 98 5 (by decide +kernel)
theorem q23_99:ThresholdAt 23 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 99 0 (by decide +kernel)
 · exact S 23 99 1 (by decide +kernel)
 · exact S 23 99 2 (by decide +kernel)
 · exact S 23 99 3 (by decide +kernel)
 · exact S 23 99 4 (by decide +kernel)
 · exact S 23 99 5 (by decide +kernel)
theorem q23_100:ThresholdAt 23 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 100 0 (by decide +kernel)
 · exact S 23 100 1 (by decide +kernel)
 · exact S 23 100 2 (by decide +kernel)
 · exact S 23 100 3 (by decide +kernel)
 · exact S 23 100 4 (by decide +kernel)
 · exact S 23 100 5 (by decide +kernel)
theorem q23_101:ThresholdAt 23 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 101 0 (by decide +kernel)
 · exact S 23 101 1 (by decide +kernel)
 · exact S 23 101 2 (by decide +kernel)
 · exact S 23 101 3 (by decide +kernel)
 · exact S 23 101 4 (by decide +kernel)
 · exact S 23 101 5 (by decide +kernel)
theorem q23_102:ThresholdAt 23 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 102 0 (by decide +kernel)
 · exact S 23 102 1 (by decide +kernel)
 · exact S 23 102 2 (by decide +kernel)
 · exact S 23 102 3 (by decide +kernel)
 · exact S 23 102 4 (by decide +kernel)
 · exact S 23 102 5 (by decide +kernel)
theorem q23_103:ThresholdAt 23 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 103 0 (by decide +kernel)
 · exact S 23 103 1 (by decide +kernel)
 · exact S 23 103 2 (by decide +kernel)
 · exact S 23 103 3 (by decide +kernel)
 · exact S 23 103 4 (by decide +kernel)
 · exact S 23 103 5 (by decide +kernel)
theorem q23_104:ThresholdAt 23 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 104 0 (by decide +kernel)
 · exact S 23 104 1 (by decide +kernel)
 · exact S 23 104 2 (by decide +kernel)
 · exact S 23 104 3 (by decide +kernel)
 · exact S 23 104 4 (by decide +kernel)
 · exact S 23 104 5 (by decide +kernel)
theorem q23_105:ThresholdAt 23 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 105 0 (by decide +kernel)
 · exact S 23 105 1 (by decide +kernel)
 · exact S 23 105 2 (by decide +kernel)
 · exact S 23 105 3 (by decide +kernel)
 · exact S 23 105 4 (by decide +kernel)
 · exact S 23 105 5 (by decide +kernel)
theorem q23_106:ThresholdAt 23 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 106 0 (by decide +kernel)
 · exact S 23 106 1 (by decide +kernel)
 · exact S 23 106 2 (by decide +kernel)
 · exact S 23 106 3 (by decide +kernel)
 · exact S 23 106 4 (by decide +kernel)
 · exact S 23 106 5 (by decide +kernel)
theorem q23_107:ThresholdAt 23 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 107 0 (by decide +kernel)
 · exact S 23 107 1 (by decide +kernel)
 · exact S 23 107 2 (by decide +kernel)
 · exact S 23 107 3 (by decide +kernel)
 · exact S 23 107 4 (by decide +kernel)
 · exact S 23 107 5 (by decide +kernel)
theorem q23_108:ThresholdAt 23 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 108 0 (by decide +kernel)
 · exact S 23 108 1 (by decide +kernel)
 · exact S 23 108 2 (by decide +kernel)
 · exact S 23 108 3 (by decide +kernel)
 · exact S 23 108 4 (by decide +kernel)
 · exact S 23 108 5 (by decide +kernel)
theorem q23_109:ThresholdAt 23 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 109 0 (by decide +kernel)
 · exact S 23 109 1 (by decide +kernel)
 · exact S 23 109 2 (by decide +kernel)
 · exact S 23 109 3 (by decide +kernel)
 · exact S 23 109 4 (by decide +kernel)
 · exact S 23 109 5 (by decide +kernel)
theorem q23_110:ThresholdAt 23 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 110 0 (by decide +kernel)
 · exact S 23 110 1 (by decide +kernel)
 · exact S 23 110 2 (by decide +kernel)
 · exact S 23 110 3 (by decide +kernel)
 · exact S 23 110 4 (by decide +kernel)
 · exact S 23 110 5 (by decide +kernel)
theorem q23_111:ThresholdAt 23 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 111 0 (by decide +kernel)
 · exact S 23 111 1 (by decide +kernel)
 · exact S 23 111 2 (by decide +kernel)
 · exact S 23 111 3 (by decide +kernel)
 · exact S 23 111 4 (by decide +kernel)
 · exact S 23 111 5 (by decide +kernel)
theorem q23_112:ThresholdAt 23 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 112 0 (by decide +kernel)
 · exact S 23 112 1 (by decide +kernel)
 · exact S 23 112 2 (by decide +kernel)
 · exact S 23 112 3 (by decide +kernel)
 · exact S 23 112 4 (by decide +kernel)
 · exact S 23 112 5 (by decide +kernel)
theorem q23_113:ThresholdAt 23 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 113 0 (by decide +kernel)
 · exact S 23 113 1 (by decide +kernel)
 · exact S 23 113 2 (by decide +kernel)
 · exact S 23 113 3 (by decide +kernel)
 · exact S 23 113 4 (by decide +kernel)
 · exact S 23 113 5 (by decide +kernel)
theorem q23_114:ThresholdAt 23 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 114 0 (by decide +kernel)
 · exact S 23 114 1 (by decide +kernel)
 · exact S 23 114 2 (by decide +kernel)
 · exact S 23 114 3 (by decide +kernel)
 · exact S 23 114 4 (by decide +kernel)
 · exact S 23 114 5 (by decide +kernel)
theorem q23_115:ThresholdAt 23 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 115 0 (by decide +kernel)
 · exact S 23 115 1 (by decide +kernel)
 · exact S 23 115 2 (by decide +kernel)
 · exact S 23 115 3 (by decide +kernel)
 · exact S 23 115 4 (by decide +kernel)
 · exact S 23 115 5 (by decide +kernel)
theorem q23_116:ThresholdAt 23 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 116 0 (by decide +kernel)
 · exact S 23 116 1 (by decide +kernel)
 · exact S 23 116 2 (by decide +kernel)
 · exact S 23 116 3 (by decide +kernel)
 · exact S 23 116 4 (by decide +kernel)
 · exact S 23 116 5 (by decide +kernel)
theorem q23_117:ThresholdAt 23 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 117 0 (by decide +kernel)
 · exact S 23 117 1 (by decide +kernel)
 · exact S 23 117 2 (by decide +kernel)
 · exact S 23 117 3 (by decide +kernel)
 · exact S 23 117 4 (by decide +kernel)
 · exact S 23 117 5 (by decide +kernel)
theorem q23_118:ThresholdAt 23 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 118 0 (by decide +kernel)
 · exact S 23 118 1 (by decide +kernel)
 · exact S 23 118 2 (by decide +kernel)
 · exact S 23 118 3 (by decide +kernel)
 · exact S 23 118 4 (by decide +kernel)
 · exact S 23 118 5 (by decide +kernel)
theorem q23_119:ThresholdAt 23 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 23 119 0 (by decide +kernel)
 · exact S 23 119 1 (by decide +kernel)
 · exact S 23 119 2 (by decide +kernel)
 · exact S 23 119 3 (by decide +kernel)
 · exact S 23 119 4 (by decide +kernel)
 · exact S 23 119 5 (by decide +kernel)
theorem checkedR23:∀ V ∈ List.range 120,ThresholdAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0_120:V < 60
  · by_cases h0_60:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q23_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q23_1
              · have he:V = 2:=by omega
                subst V
                exact q23_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q23_3
              · have he:V = 4:=by omega
                subst V
                exact q23_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q23_5
              · have he:V = 6:=by omega
                subst V
                exact q23_6
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have he:V = 7:=by omega
                subst V
                exact q23_7
              · have he:V = 8:=by omega
                subst V
                exact q23_8
            · by_cases h9_11:V < 10
              · have he:V = 9:=by omega
                subst V
                exact q23_9
              · have he:V = 10:=by omega
                subst V
                exact q23_10
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have he:V = 11:=by omega
                subst V
                exact q23_11
              · have he:V = 12:=by omega
                subst V
                exact q23_12
            · by_cases h13_15:V < 14
              · have he:V = 13:=by omega
                subst V
                exact q23_13
              · have he:V = 14:=by omega
                subst V
                exact q23_14
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have he:V = 15:=by omega
              subst V
              exact q23_15
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q23_16
              · have he:V = 17:=by omega
                subst V
                exact q23_17
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q23_18
              · have he:V = 19:=by omega
                subst V
                exact q23_19
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q23_20
              · have he:V = 21:=by omega
                subst V
                exact q23_21
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q23_22
              · have he:V = 23:=by omega
                subst V
                exact q23_23
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q23_24
              · have he:V = 25:=by omega
                subst V
                exact q23_25
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q23_26
              · have he:V = 27:=by omega
                subst V
                exact q23_27
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q23_28
              · have he:V = 29:=by omega
                subst V
                exact q23_29
    · by_cases h30_60:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have he:V = 30:=by omega
              subst V
              exact q23_30
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q23_31
              · have he:V = 32:=by omega
                subst V
                exact q23_32
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q23_33
              · have he:V = 34:=by omega
                subst V
                exact q23_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q23_35
              · have he:V = 36:=by omega
                subst V
                exact q23_36
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q23_37
              · have he:V = 38:=by omega
                subst V
                exact q23_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q23_39
              · have he:V = 40:=by omega
                subst V
                exact q23_40
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q23_41
              · have he:V = 42:=by omega
                subst V
                exact q23_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q23_43
              · have he:V = 44:=by omega
                subst V
                exact q23_44
      · by_cases h45_60:V < 52
        · by_cases h45_52:V < 48
          · by_cases h45_48:V < 46
            · have he:V = 45:=by omega
              subst V
              exact q23_45
            · by_cases h46_48:V < 47
              · have he:V = 46:=by omega
                subst V
                exact q23_46
              · have he:V = 47:=by omega
                subst V
                exact q23_47
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have he:V = 48:=by omega
                subst V
                exact q23_48
              · have he:V = 49:=by omega
                subst V
                exact q23_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q23_50
              · have he:V = 51:=by omega
                subst V
                exact q23_51
        · by_cases h52_60:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q23_52
              · have he:V = 53:=by omega
                subst V
                exact q23_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q23_54
              · have he:V = 55:=by omega
                subst V
                exact q23_55
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have he:V = 56:=by omega
                subst V
                exact q23_56
              · have he:V = 57:=by omega
                subst V
                exact q23_57
            · by_cases h58_60:V < 59
              · have he:V = 58:=by omega
                subst V
                exact q23_58
              · have he:V = 59:=by omega
                subst V
                exact q23_59
  · by_cases h60_120:V < 90
    · by_cases h60_90:V < 75
      · by_cases h60_75:V < 67
        · by_cases h60_67:V < 63
          · by_cases h60_63:V < 61
            · have he:V = 60:=by omega
              subst V
              exact q23_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q23_61
              · have he:V = 62:=by omega
                subst V
                exact q23_62
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q23_63
              · have he:V = 64:=by omega
                subst V
                exact q23_64
            · by_cases h65_67:V < 66
              · have he:V = 65:=by omega
                subst V
                exact q23_65
              · have he:V = 66:=by omega
                subst V
                exact q23_66
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have he:V = 67:=by omega
                subst V
                exact q23_67
              · have he:V = 68:=by omega
                subst V
                exact q23_68
            · by_cases h69_71:V < 70
              · have he:V = 69:=by omega
                subst V
                exact q23_69
              · have he:V = 70:=by omega
                subst V
                exact q23_70
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q23_71
              · have he:V = 72:=by omega
                subst V
                exact q23_72
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q23_73
              · have he:V = 74:=by omega
                subst V
                exact q23_74
      · by_cases h75_90:V < 82
        · by_cases h75_82:V < 78
          · by_cases h75_78:V < 76
            · have he:V = 75:=by omega
              subst V
              exact q23_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q23_76
              · have he:V = 77:=by omega
                subst V
                exact q23_77
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q23_78
              · have he:V = 79:=by omega
                subst V
                exact q23_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q23_80
              · have he:V = 81:=by omega
                subst V
                exact q23_81
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q23_82
              · have he:V = 83:=by omega
                subst V
                exact q23_83
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q23_84
              · have he:V = 85:=by omega
                subst V
                exact q23_85
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q23_86
              · have he:V = 87:=by omega
                subst V
                exact q23_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q23_88
              · have he:V = 89:=by omega
                subst V
                exact q23_89
    · by_cases h90_120:V < 105
      · by_cases h90_105:V < 97
        · by_cases h90_97:V < 93
          · by_cases h90_93:V < 91
            · have he:V = 90:=by omega
              subst V
              exact q23_90
            · by_cases h91_93:V < 92
              · have he:V = 91:=by omega
                subst V
                exact q23_91
              · have he:V = 92:=by omega
                subst V
                exact q23_92
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have he:V = 93:=by omega
                subst V
                exact q23_93
              · have he:V = 94:=by omega
                subst V
                exact q23_94
            · by_cases h95_97:V < 96
              · have he:V = 95:=by omega
                subst V
                exact q23_95
              · have he:V = 96:=by omega
                subst V
                exact q23_96
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have he:V = 97:=by omega
                subst V
                exact q23_97
              · have he:V = 98:=by omega
                subst V
                exact q23_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q23_99
              · have he:V = 100:=by omega
                subst V
                exact q23_100
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q23_101
              · have he:V = 102:=by omega
                subst V
                exact q23_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q23_103
              · have he:V = 104:=by omega
                subst V
                exact q23_104
      · by_cases h105_120:V < 112
        · by_cases h105_112:V < 108
          · by_cases h105_108:V < 106
            · have he:V = 105:=by omega
              subst V
              exact q23_105
            · by_cases h106_108:V < 107
              · have he:V = 106:=by omega
                subst V
                exact q23_106
              · have he:V = 107:=by omega
                subst V
                exact q23_107
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have he:V = 108:=by omega
                subst V
                exact q23_108
              · have he:V = 109:=by omega
                subst V
                exact q23_109
            · by_cases h110_112:V < 111
              · have he:V = 110:=by omega
                subst V
                exact q23_110
              · have he:V = 111:=by omega
                subst V
                exact q23_111
        · by_cases h112_120:V < 116
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have he:V = 112:=by omega
                subst V
                exact q23_112
              · have he:V = 113:=by omega
                subst V
                exact q23_113
            · by_cases h114_116:V < 115
              · have he:V = 114:=by omega
                subst V
                exact q23_114
              · have he:V = 115:=by omega
                subst V
                exact q23_115
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have he:V = 116:=by omega
                subst V
                exact q23_116
              · have he:V = 117:=by omega
                subst V
                exact q23_117
            · by_cases h118_120:V < 119
              · have he:V = 118:=by omega
                subst V
                exact q23_118
              · have he:V = 119:=by omega
                subst V
                exact q23_119
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
