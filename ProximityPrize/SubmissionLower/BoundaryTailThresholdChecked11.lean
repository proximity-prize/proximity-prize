import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked10

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q11_0:ThresholdAt 11 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 0 0 (by decide +kernel)
 · exact S 11 0 1 (by decide +kernel)
 · exact S 11 0 2 (by decide +kernel)
 · exact S 11 0 3 (by decide +kernel)
 · exact S 11 0 4 (by decide +kernel)
 · exact S 11 0 5 (by decide +kernel)
theorem q11_1:ThresholdAt 11 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 1 0 (by decide +kernel)
 · exact S 11 1 1 (by decide +kernel)
 · exact S 11 1 2 (by decide +kernel)
 · exact S 11 1 3 (by decide +kernel)
 · exact S 11 1 4 (by decide +kernel)
 · exact S 11 1 5 (by decide +kernel)
theorem q11_2:ThresholdAt 11 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 2 0 (by decide +kernel)
 · exact S 11 2 1 (by decide +kernel)
 · exact S 11 2 2 (by decide +kernel)
 · exact S 11 2 3 (by decide +kernel)
 · exact S 11 2 4 (by decide +kernel)
 · exact S 11 2 5 (by decide +kernel)
theorem q11_3:ThresholdAt 11 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 3 0 (by decide +kernel)
 · exact S 11 3 1 (by decide +kernel)
 · exact S 11 3 2 (by decide +kernel)
 · exact S 11 3 3 (by decide +kernel)
 · exact S 11 3 4 (by decide +kernel)
 · exact S 11 3 5 (by decide +kernel)
theorem q11_4:ThresholdAt 11 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 4 0 (by decide +kernel)
 · exact S 11 4 1 (by decide +kernel)
 · exact S 11 4 2 (by decide +kernel)
 · exact S 11 4 3 (by decide +kernel)
 · exact S 11 4 4 (by decide +kernel)
 · exact S 11 4 5 (by decide +kernel)
theorem q11_5:ThresholdAt 11 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 5 0 (by decide +kernel)
 · exact S 11 5 1 (by decide +kernel)
 · exact S 11 5 2 (by decide +kernel)
 · exact S 11 5 3 (by decide +kernel)
 · exact S 11 5 4 (by decide +kernel)
 · exact S 11 5 5 (by decide +kernel)
theorem q11_6:ThresholdAt 11 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 6 0 (by decide +kernel)
 · exact S 11 6 1 (by decide +kernel)
 · exact S 11 6 2 (by decide +kernel)
 · exact S 11 6 3 (by decide +kernel)
 · exact S 11 6 4 (by decide +kernel)
 · exact S 11 6 5 (by decide +kernel)
theorem q11_7:ThresholdAt 11 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 7 0 (by decide +kernel)
 · exact S 11 7 1 (by decide +kernel)
 · exact S 11 7 2 (by decide +kernel)
 · exact S 11 7 3 (by decide +kernel)
 · exact S 11 7 4 (by decide +kernel)
 · exact S 11 7 5 (by decide +kernel)
theorem q11_8:ThresholdAt 11 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 8 0 (by decide +kernel)
 · exact S 11 8 1 (by decide +kernel)
 · exact S 11 8 2 (by decide +kernel)
 · exact S 11 8 3 (by decide +kernel)
 · exact S 11 8 4 (by decide +kernel)
 · exact S 11 8 5 (by decide +kernel)
theorem q11_9:ThresholdAt 11 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 9 0 (by decide +kernel)
 · exact S 11 9 1 (by decide +kernel)
 · exact S 11 9 2 (by decide +kernel)
 · exact S 11 9 3 (by decide +kernel)
 · exact S 11 9 4 (by decide +kernel)
 · exact S 11 9 5 (by decide +kernel)
theorem q11_10:ThresholdAt 11 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 10 0 (by decide +kernel)
 · exact S 11 10 1 (by decide +kernel)
 · exact S 11 10 2 (by decide +kernel)
 · exact S 11 10 3 (by decide +kernel)
 · exact S 11 10 4 (by decide +kernel)
 · exact S 11 10 5 (by decide +kernel)
theorem q11_11:ThresholdAt 11 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 11 0 (by decide +kernel)
 · exact S 11 11 1 (by decide +kernel)
 · exact S 11 11 2 (by decide +kernel)
 · exact S 11 11 3 (by decide +kernel)
 · exact S 11 11 4 (by decide +kernel)
 · exact S 11 11 5 (by decide +kernel)
theorem q11_12:ThresholdAt 11 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 12 0 (by decide +kernel)
 · exact S 11 12 1 (by decide +kernel)
 · exact S 11 12 2 (by decide +kernel)
 · exact S 11 12 3 (by decide +kernel)
 · exact S 11 12 4 (by decide +kernel)
 · exact S 11 12 5 (by decide +kernel)
theorem q11_13:ThresholdAt 11 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 13 0 (by decide +kernel)
 · exact S 11 13 1 (by decide +kernel)
 · exact S 11 13 2 (by decide +kernel)
 · exact S 11 13 3 (by decide +kernel)
 · exact S 11 13 4 (by decide +kernel)
 · exact S 11 13 5 (by decide +kernel)
theorem q11_14:ThresholdAt 11 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 14 0 (by decide +kernel)
 · exact S 11 14 1 (by decide +kernel)
 · exact S 11 14 2 (by decide +kernel)
 · exact S 11 14 3 (by decide +kernel)
 · exact S 11 14 4 (by decide +kernel)
 · exact S 11 14 5 (by decide +kernel)
theorem q11_15:ThresholdAt 11 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 15 0 (by decide +kernel)
 · exact S 11 15 1 (by decide +kernel)
 · exact S 11 15 2 (by decide +kernel)
 · exact S 11 15 3 (by decide +kernel)
 · exact S 11 15 4 (by decide +kernel)
 · exact S 11 15 5 (by decide +kernel)
theorem q11_16:ThresholdAt 11 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 16 0 (by decide +kernel)
 · exact S 11 16 1 (by decide +kernel)
 · exact S 11 16 2 (by decide +kernel)
 · exact S 11 16 3 (by decide +kernel)
 · exact S 11 16 4 (by decide +kernel)
 · exact S 11 16 5 (by decide +kernel)
theorem q11_17:ThresholdAt 11 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 17 0 (by decide +kernel)
 · exact S 11 17 1 (by decide +kernel)
 · exact S 11 17 2 (by decide +kernel)
 · exact S 11 17 3 (by decide +kernel)
 · exact S 11 17 4 (by decide +kernel)
 · exact S 11 17 5 (by decide +kernel)
theorem q11_18:ThresholdAt 11 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 18 0 (by decide +kernel)
 · exact S 11 18 1 (by decide +kernel)
 · exact S 11 18 2 (by decide +kernel)
 · exact S 11 18 3 (by decide +kernel)
 · exact S 11 18 4 (by decide +kernel)
 · exact S 11 18 5 (by decide +kernel)
theorem q11_19:ThresholdAt 11 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 19 0 (by decide +kernel)
 · exact S 11 19 1 (by decide +kernel)
 · exact S 11 19 2 (by decide +kernel)
 · exact S 11 19 3 (by decide +kernel)
 · exact S 11 19 4 (by decide +kernel)
 · exact S 11 19 5 (by decide +kernel)
theorem q11_20:ThresholdAt 11 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 20 0 (by decide +kernel)
 · exact S 11 20 1 (by decide +kernel)
 · exact S 11 20 2 (by decide +kernel)
 · exact S 11 20 3 (by decide +kernel)
 · exact S 11 20 4 (by decide +kernel)
 · exact S 11 20 5 (by decide +kernel)
theorem q11_21:ThresholdAt 11 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 21 0 (by decide +kernel)
 · exact S 11 21 1 (by decide +kernel)
 · exact S 11 21 2 (by decide +kernel)
 · exact S 11 21 3 (by decide +kernel)
 · exact S 11 21 4 (by decide +kernel)
 · exact S 11 21 5 (by decide +kernel)
theorem q11_22:ThresholdAt 11 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 22 0 (by decide +kernel)
 · exact S 11 22 1 (by decide +kernel)
 · exact S 11 22 2 (by decide +kernel)
 · exact S 11 22 3 (by decide +kernel)
 · exact S 11 22 4 (by decide +kernel)
 · exact S 11 22 5 (by decide +kernel)
theorem q11_23:ThresholdAt 11 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 23 0 (by decide +kernel)
 · exact S 11 23 1 (by decide +kernel)
 · exact S 11 23 2 (by decide +kernel)
 · exact S 11 23 3 (by decide +kernel)
 · exact S 11 23 4 (by decide +kernel)
 · exact S 11 23 5 (by decide +kernel)
theorem q11_24:ThresholdAt 11 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 24 0 (by decide +kernel)
 · exact S 11 24 1 (by decide +kernel)
 · exact S 11 24 2 (by decide +kernel)
 · exact S 11 24 3 (by decide +kernel)
 · exact S 11 24 4 (by decide +kernel)
 · exact S 11 24 5 (by decide +kernel)
theorem q11_25:ThresholdAt 11 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 25 0 (by decide +kernel)
 · exact S 11 25 1 (by decide +kernel)
 · exact S 11 25 2 (by decide +kernel)
 · exact S 11 25 3 (by decide +kernel)
 · exact S 11 25 4 (by decide +kernel)
 · exact S 11 25 5 (by decide +kernel)
theorem q11_26:ThresholdAt 11 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 26 0 (by decide +kernel)
 · exact S 11 26 1 (by decide +kernel)
 · exact S 11 26 2 (by decide +kernel)
 · exact S 11 26 3 (by decide +kernel)
 · exact S 11 26 4 (by decide +kernel)
 · exact S 11 26 5 (by decide +kernel)
theorem q11_27:ThresholdAt 11 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 27 0 (by decide +kernel)
 · exact S 11 27 1 (by decide +kernel)
 · exact S 11 27 2 (by decide +kernel)
 · exact S 11 27 3 (by decide +kernel)
 · exact S 11 27 4 (by decide +kernel)
 · exact S 11 27 5 (by decide +kernel)
theorem q11_28:ThresholdAt 11 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 28 0 (by decide +kernel)
 · exact S 11 28 1 (by decide +kernel)
 · exact S 11 28 2 (by decide +kernel)
 · exact S 11 28 3 (by decide +kernel)
 · exact S 11 28 4 (by decide +kernel)
 · exact S 11 28 5 (by decide +kernel)
theorem q11_29:ThresholdAt 11 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 29 0 (by decide +kernel)
 · exact S 11 29 1 (by decide +kernel)
 · exact S 11 29 2 (by decide +kernel)
 · exact S 11 29 3 (by decide +kernel)
 · exact S 11 29 4 (by decide +kernel)
 · exact S 11 29 5 (by decide +kernel)
theorem q11_30:ThresholdAt 11 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 30 0 (by decide +kernel)
 · exact S 11 30 1 (by decide +kernel)
 · exact S 11 30 2 (by decide +kernel)
 · exact S 11 30 3 (by decide +kernel)
 · exact S 11 30 4 (by decide +kernel)
 · exact S 11 30 5 (by decide +kernel)
theorem q11_31:ThresholdAt 11 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 31 0 (by decide +kernel)
 · exact S 11 31 1 (by decide +kernel)
 · exact S 11 31 2 (by decide +kernel)
 · exact S 11 31 3 (by decide +kernel)
 · exact S 11 31 4 (by decide +kernel)
 · exact S 11 31 5 (by decide +kernel)
theorem q11_32:ThresholdAt 11 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 32 0 (by decide +kernel)
 · exact S 11 32 1 (by decide +kernel)
 · exact S 11 32 2 (by decide +kernel)
 · exact S 11 32 3 (by decide +kernel)
 · exact S 11 32 4 (by decide +kernel)
 · exact S 11 32 5 (by decide +kernel)
theorem q11_33:ThresholdAt 11 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 33 0 (by decide +kernel)
 · exact S 11 33 1 (by decide +kernel)
 · exact S 11 33 2 (by decide +kernel)
 · exact S 11 33 3 (by decide +kernel)
 · exact S 11 33 4 (by decide +kernel)
 · exact S 11 33 5 (by decide +kernel)
theorem q11_34:ThresholdAt 11 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 34 0 (by decide +kernel)
 · exact S 11 34 1 (by decide +kernel)
 · exact S 11 34 2 (by decide +kernel)
 · exact S 11 34 3 (by decide +kernel)
 · exact S 11 34 4 (by decide +kernel)
 · exact S 11 34 5 (by decide +kernel)
theorem q11_35:ThresholdAt 11 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 35 0 (by decide +kernel)
 · exact S 11 35 1 (by decide +kernel)
 · exact S 11 35 2 (by decide +kernel)
 · exact S 11 35 3 (by decide +kernel)
 · exact S 11 35 4 (by decide +kernel)
 · exact S 11 35 5 (by decide +kernel)
theorem q11_36:ThresholdAt 11 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 36 0 (by decide +kernel)
 · exact S 11 36 1 (by decide +kernel)
 · exact S 11 36 2 (by decide +kernel)
 · exact S 11 36 3 (by decide +kernel)
 · exact S 11 36 4 (by decide +kernel)
 · exact S 11 36 5 (by decide +kernel)
theorem q11_37:ThresholdAt 11 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 37 0 (by decide +kernel)
 · exact S 11 37 1 (by decide +kernel)
 · exact S 11 37 2 (by decide +kernel)
 · exact S 11 37 3 (by decide +kernel)
 · exact S 11 37 4 (by decide +kernel)
 · exact S 11 37 5 (by decide +kernel)
theorem q11_38:ThresholdAt 11 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 38 0 (by decide +kernel)
 · exact S 11 38 1 (by decide +kernel)
 · exact S 11 38 2 (by decide +kernel)
 · exact S 11 38 3 (by decide +kernel)
 · exact S 11 38 4 (by decide +kernel)
 · exact S 11 38 5 (by decide +kernel)
theorem q11_39:ThresholdAt 11 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 39 0 (by decide +kernel)
 · exact S 11 39 1 (by decide +kernel)
 · exact S 11 39 2 (by decide +kernel)
 · exact S 11 39 3 (by decide +kernel)
 · exact S 11 39 4 (by decide +kernel)
 · exact S 11 39 5 (by decide +kernel)
theorem q11_40:ThresholdAt 11 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 40 0 (by decide +kernel)
 · exact S 11 40 1 (by decide +kernel)
 · exact S 11 40 2 (by decide +kernel)
 · exact S 11 40 3 (by decide +kernel)
 · exact S 11 40 4 (by decide +kernel)
 · exact S 11 40 5 (by decide +kernel)
theorem q11_41:ThresholdAt 11 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 41 0 (by decide +kernel)
 · exact S 11 41 1 (by decide +kernel)
 · exact S 11 41 2 (by decide +kernel)
 · exact S 11 41 3 (by decide +kernel)
 · exact S 11 41 4 (by decide +kernel)
 · exact S 11 41 5 (by decide +kernel)
theorem q11_42:ThresholdAt 11 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 42 0 (by decide +kernel)
 · exact S 11 42 1 (by decide +kernel)
 · exact S 11 42 2 (by decide +kernel)
 · exact S 11 42 3 (by decide +kernel)
 · exact S 11 42 4 (by decide +kernel)
 · exact S 11 42 5 (by decide +kernel)
theorem q11_43:ThresholdAt 11 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 43 0 (by decide +kernel)
 · exact S 11 43 1 (by decide +kernel)
 · exact S 11 43 2 (by decide +kernel)
 · exact S 11 43 3 (by decide +kernel)
 · exact S 11 43 4 (by decide +kernel)
 · exact S 11 43 5 (by decide +kernel)
theorem q11_44:ThresholdAt 11 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 44 0 (by decide +kernel)
 · exact S 11 44 1 (by decide +kernel)
 · exact S 11 44 2 (by decide +kernel)
 · exact S 11 44 3 (by decide +kernel)
 · exact S 11 44 4 (by decide +kernel)
 · exact S 11 44 5 (by decide +kernel)
theorem q11_45:ThresholdAt 11 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 45 0 (by decide +kernel)
 · exact S 11 45 1 (by decide +kernel)
 · exact S 11 45 2 (by decide +kernel)
 · exact S 11 45 3 (by decide +kernel)
 · exact S 11 45 4 (by decide +kernel)
 · exact S 11 45 5 (by decide +kernel)
theorem q11_46:ThresholdAt 11 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 46 0 (by decide +kernel)
 · exact S 11 46 1 (by decide +kernel)
 · exact S 11 46 2 (by decide +kernel)
 · exact S 11 46 3 (by decide +kernel)
 · exact S 11 46 4 (by decide +kernel)
 · exact S 11 46 5 (by decide +kernel)
theorem q11_47:ThresholdAt 11 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 47 0 (by decide +kernel)
 · exact S 11 47 1 (by decide +kernel)
 · exact S 11 47 2 (by decide +kernel)
 · exact S 11 47 3 (by decide +kernel)
 · exact S 11 47 4 (by decide +kernel)
 · exact S 11 47 5 (by decide +kernel)
theorem q11_48:ThresholdAt 11 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 48 0 (by decide +kernel)
 · exact S 11 48 1 (by decide +kernel)
 · exact S 11 48 2 (by decide +kernel)
 · exact S 11 48 3 (by decide +kernel)
 · exact S 11 48 4 (by decide +kernel)
 · exact S 11 48 5 (by decide +kernel)
theorem q11_49:ThresholdAt 11 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 49 0 (by decide +kernel)
 · exact S 11 49 1 (by decide +kernel)
 · exact S 11 49 2 (by decide +kernel)
 · exact S 11 49 3 (by decide +kernel)
 · exact S 11 49 4 (by decide +kernel)
 · exact S 11 49 5 (by decide +kernel)
theorem q11_50:ThresholdAt 11 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 50 0 (by decide +kernel)
 · exact S 11 50 1 (by decide +kernel)
 · exact S 11 50 2 (by decide +kernel)
 · exact S 11 50 3 (by decide +kernel)
 · exact S 11 50 4 (by decide +kernel)
 · exact S 11 50 5 (by decide +kernel)
theorem q11_51:ThresholdAt 11 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 51 0 (by decide +kernel)
 · exact S 11 51 1 (by decide +kernel)
 · exact S 11 51 2 (by decide +kernel)
 · exact S 11 51 3 (by decide +kernel)
 · exact S 11 51 4 (by decide +kernel)
 · exact S 11 51 5 (by decide +kernel)
theorem q11_52:ThresholdAt 11 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 52 0 (by decide +kernel)
 · exact S 11 52 1 (by decide +kernel)
 · exact S 11 52 2 (by decide +kernel)
 · exact S 11 52 3 (by decide +kernel)
 · exact S 11 52 4 (by decide +kernel)
 · exact S 11 52 5 (by decide +kernel)
theorem q11_53:ThresholdAt 11 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 53 0 (by decide +kernel)
 · exact S 11 53 1 (by decide +kernel)
 · exact S 11 53 2 (by decide +kernel)
 · exact S 11 53 3 (by decide +kernel)
 · exact S 11 53 4 (by decide +kernel)
 · exact S 11 53 5 (by decide +kernel)
theorem q11_54:ThresholdAt 11 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 54 0 (by decide +kernel)
 · exact S 11 54 1 (by decide +kernel)
 · exact S 11 54 2 (by decide +kernel)
 · exact S 11 54 3 (by decide +kernel)
 · exact S 11 54 4 (by decide +kernel)
 · exact S 11 54 5 (by decide +kernel)
theorem q11_55:ThresholdAt 11 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 55 0 (by decide +kernel)
 · exact S 11 55 1 (by decide +kernel)
 · exact S 11 55 2 (by decide +kernel)
 · exact S 11 55 3 (by decide +kernel)
 · exact S 11 55 4 (by decide +kernel)
 · exact S 11 55 5 (by decide +kernel)
theorem q11_56:ThresholdAt 11 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 56 0 (by decide +kernel)
 · exact S 11 56 1 (by decide +kernel)
 · exact S 11 56 2 (by decide +kernel)
 · exact S 11 56 3 (by decide +kernel)
 · exact S 11 56 4 (by decide +kernel)
 · exact S 11 56 5 (by decide +kernel)
theorem q11_57:ThresholdAt 11 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 57 0 (by decide +kernel)
 · exact S 11 57 1 (by decide +kernel)
 · exact S 11 57 2 (by decide +kernel)
 · exact S 11 57 3 (by decide +kernel)
 · exact S 11 57 4 (by decide +kernel)
 · exact S 11 57 5 (by decide +kernel)
theorem q11_58:ThresholdAt 11 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 58 0 (by decide +kernel)
 · exact S 11 58 1 (by decide +kernel)
 · exact S 11 58 2 (by decide +kernel)
 · exact S 11 58 3 (by decide +kernel)
 · exact S 11 58 4 (by decide +kernel)
 · exact S 11 58 5 (by decide +kernel)
theorem q11_59:ThresholdAt 11 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 59 0 (by decide +kernel)
 · exact S 11 59 1 (by decide +kernel)
 · exact S 11 59 2 (by decide +kernel)
 · exact S 11 59 3 (by decide +kernel)
 · exact S 11 59 4 (by decide +kernel)
 · exact S 11 59 5 (by decide +kernel)
theorem q11_60:ThresholdAt 11 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 60 0 (by decide +kernel)
 · exact S 11 60 1 (by decide +kernel)
 · exact S 11 60 2 (by decide +kernel)
 · exact S 11 60 3 (by decide +kernel)
 · exact S 11 60 4 (by decide +kernel)
 · exact S 11 60 5 (by decide +kernel)
theorem q11_61:ThresholdAt 11 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 61 0 (by decide +kernel)
 · exact S 11 61 1 (by decide +kernel)
 · exact S 11 61 2 (by decide +kernel)
 · exact S 11 61 3 (by decide +kernel)
 · exact S 11 61 4 (by decide +kernel)
 · exact S 11 61 5 (by decide +kernel)
theorem q11_62:ThresholdAt 11 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 62 0 (by decide +kernel)
 · exact S 11 62 1 (by decide +kernel)
 · exact S 11 62 2 (by decide +kernel)
 · exact S 11 62 3 (by decide +kernel)
 · exact S 11 62 4 (by decide +kernel)
 · exact S 11 62 5 (by decide +kernel)
theorem q11_63:ThresholdAt 11 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 63 0 (by decide +kernel)
 · exact S 11 63 1 (by decide +kernel)
 · exact S 11 63 2 (by decide +kernel)
 · exact S 11 63 3 (by decide +kernel)
 · exact S 11 63 4 (by decide +kernel)
 · exact S 11 63 5 (by decide +kernel)
theorem q11_64:ThresholdAt 11 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 64 0 (by decide +kernel)
 · exact S 11 64 1 (by decide +kernel)
 · exact S 11 64 2 (by decide +kernel)
 · exact S 11 64 3 (by decide +kernel)
 · exact S 11 64 4 (by decide +kernel)
 · exact S 11 64 5 (by decide +kernel)
theorem q11_65:ThresholdAt 11 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 65 0 (by decide +kernel)
 · exact S 11 65 1 (by decide +kernel)
 · exact S 11 65 2 (by decide +kernel)
 · exact S 11 65 3 (by decide +kernel)
 · exact S 11 65 4 (by decide +kernel)
 · exact S 11 65 5 (by decide +kernel)
theorem q11_66:ThresholdAt 11 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 66 0 (by decide +kernel)
 · exact S 11 66 1 (by decide +kernel)
 · exact S 11 66 2 (by decide +kernel)
 · exact S 11 66 3 (by decide +kernel)
 · exact S 11 66 4 (by decide +kernel)
 · exact S 11 66 5 (by decide +kernel)
theorem q11_67:ThresholdAt 11 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 67 0 (by decide +kernel)
 · exact S 11 67 1 (by decide +kernel)
 · exact S 11 67 2 (by decide +kernel)
 · exact S 11 67 3 (by decide +kernel)
 · exact S 11 67 4 (by decide +kernel)
 · exact S 11 67 5 (by decide +kernel)
theorem q11_68:ThresholdAt 11 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 68 0 (by decide +kernel)
 · exact S 11 68 1 (by decide +kernel)
 · exact S 11 68 2 (by decide +kernel)
 · exact S 11 68 3 (by decide +kernel)
 · exact S 11 68 4 (by decide +kernel)
 · exact S 11 68 5 (by decide +kernel)
theorem q11_69:ThresholdAt 11 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 69 0 (by decide +kernel)
 · exact S 11 69 1 (by decide +kernel)
 · exact S 11 69 2 (by decide +kernel)
 · exact S 11 69 3 (by decide +kernel)
 · exact S 11 69 4 (by decide +kernel)
 · exact S 11 69 5 (by decide +kernel)
theorem q11_70:ThresholdAt 11 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 70 0 (by decide +kernel)
 · exact S 11 70 1 (by decide +kernel)
 · exact S 11 70 2 (by decide +kernel)
 · exact S 11 70 3 (by decide +kernel)
 · exact S 11 70 4 (by decide +kernel)
 · exact S 11 70 5 (by decide +kernel)
theorem q11_71:ThresholdAt 11 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 71 0 (by decide +kernel)
 · exact S 11 71 1 (by decide +kernel)
 · exact S 11 71 2 (by decide +kernel)
 · exact S 11 71 3 (by decide +kernel)
 · exact S 11 71 4 (by decide +kernel)
 · exact S 11 71 5 (by decide +kernel)
theorem q11_72:ThresholdAt 11 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 72 0 (by decide +kernel)
 · exact S 11 72 1 (by decide +kernel)
 · exact S 11 72 2 (by decide +kernel)
 · exact S 11 72 3 (by decide +kernel)
 · exact S 11 72 4 (by decide +kernel)
 · exact S 11 72 5 (by decide +kernel)
theorem q11_73:ThresholdAt 11 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 73 0 (by decide +kernel)
 · exact S 11 73 1 (by decide +kernel)
 · exact S 11 73 2 (by decide +kernel)
 · exact S 11 73 3 (by decide +kernel)
 · exact S 11 73 4 (by decide +kernel)
 · exact S 11 73 5 (by decide +kernel)
theorem q11_74:ThresholdAt 11 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 74 0 (by decide +kernel)
 · exact S 11 74 1 (by decide +kernel)
 · exact S 11 74 2 (by decide +kernel)
 · exact S 11 74 3 (by decide +kernel)
 · exact S 11 74 4 (by decide +kernel)
 · exact S 11 74 5 (by decide +kernel)
theorem q11_75:ThresholdAt 11 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 75 0 (by decide +kernel)
 · exact S 11 75 1 (by decide +kernel)
 · exact S 11 75 2 (by decide +kernel)
 · exact S 11 75 3 (by decide +kernel)
 · exact S 11 75 4 (by decide +kernel)
 · exact S 11 75 5 (by decide +kernel)
theorem q11_76:ThresholdAt 11 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 76 0 (by decide +kernel)
 · exact S 11 76 1 (by decide +kernel)
 · exact S 11 76 2 (by decide +kernel)
 · exact S 11 76 3 (by decide +kernel)
 · exact S 11 76 4 (by decide +kernel)
 · exact S 11 76 5 (by decide +kernel)
theorem q11_77:ThresholdAt 11 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 77 0 (by decide +kernel)
 · exact S 11 77 1 (by decide +kernel)
 · exact S 11 77 2 (by decide +kernel)
 · exact S 11 77 3 (by decide +kernel)
 · exact S 11 77 4 (by decide +kernel)
 · exact S 11 77 5 (by decide +kernel)
theorem q11_78:ThresholdAt 11 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 78 0 (by decide +kernel)
 · exact S 11 78 1 (by decide +kernel)
 · exact S 11 78 2 (by decide +kernel)
 · exact S 11 78 3 (by decide +kernel)
 · exact S 11 78 4 (by decide +kernel)
 · exact S 11 78 5 (by decide +kernel)
theorem q11_79:ThresholdAt 11 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 79 0 (by decide +kernel)
 · exact S 11 79 1 (by decide +kernel)
 · exact S 11 79 2 (by decide +kernel)
 · exact S 11 79 3 (by decide +kernel)
 · exact S 11 79 4 (by decide +kernel)
 · exact S 11 79 5 (by decide +kernel)
theorem q11_80:ThresholdAt 11 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 80 0 (by decide +kernel)
 · exact S 11 80 1 (by decide +kernel)
 · exact S 11 80 2 (by decide +kernel)
 · exact S 11 80 3 (by decide +kernel)
 · exact S 11 80 4 (by decide +kernel)
 · exact S 11 80 5 (by decide +kernel)
theorem q11_81:ThresholdAt 11 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 81 0 (by decide +kernel)
 · exact S 11 81 1 (by decide +kernel)
 · exact S 11 81 2 (by decide +kernel)
 · exact S 11 81 3 (by decide +kernel)
 · exact S 11 81 4 (by decide +kernel)
 · exact S 11 81 5 (by decide +kernel)
theorem q11_82:ThresholdAt 11 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 82 0 (by decide +kernel)
 · exact S 11 82 1 (by decide +kernel)
 · exact S 11 82 2 (by decide +kernel)
 · exact S 11 82 3 (by decide +kernel)
 · exact S 11 82 4 (by decide +kernel)
 · exact S 11 82 5 (by decide +kernel)
theorem q11_83:ThresholdAt 11 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 83 0 (by decide +kernel)
 · exact S 11 83 1 (by decide +kernel)
 · exact S 11 83 2 (by decide +kernel)
 · exact S 11 83 3 (by decide +kernel)
 · exact S 11 83 4 (by decide +kernel)
 · exact S 11 83 5 (by decide +kernel)
theorem q11_84:ThresholdAt 11 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 84 0 (by decide +kernel)
 · exact S 11 84 1 (by decide +kernel)
 · exact S 11 84 2 (by decide +kernel)
 · exact S 11 84 3 (by decide +kernel)
 · exact S 11 84 4 (by decide +kernel)
 · exact S 11 84 5 (by decide +kernel)
theorem q11_85:ThresholdAt 11 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 85 0 (by decide +kernel)
 · exact S 11 85 1 (by decide +kernel)
 · exact S 11 85 2 (by decide +kernel)
 · exact S 11 85 3 (by decide +kernel)
 · exact S 11 85 4 (by decide +kernel)
 · exact S 11 85 5 (by decide +kernel)
theorem q11_86:ThresholdAt 11 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 86 0 (by decide +kernel)
 · exact S 11 86 1 (by decide +kernel)
 · exact S 11 86 2 (by decide +kernel)
 · exact S 11 86 3 (by decide +kernel)
 · exact S 11 86 4 (by decide +kernel)
 · exact S 11 86 5 (by decide +kernel)
theorem q11_87:ThresholdAt 11 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 87 0 (by decide +kernel)
 · exact S 11 87 1 (by decide +kernel)
 · exact S 11 87 2 (by decide +kernel)
 · exact S 11 87 3 (by decide +kernel)
 · exact S 11 87 4 (by decide +kernel)
 · exact S 11 87 5 (by decide +kernel)
theorem q11_88:ThresholdAt 11 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 88 0 (by decide +kernel)
 · exact S 11 88 1 (by decide +kernel)
 · exact S 11 88 2 (by decide +kernel)
 · exact S 11 88 3 (by decide +kernel)
 · exact S 11 88 4 (by decide +kernel)
 · exact S 11 88 5 (by decide +kernel)
theorem q11_89:ThresholdAt 11 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 89 0 (by decide +kernel)
 · exact S 11 89 1 (by decide +kernel)
 · exact S 11 89 2 (by decide +kernel)
 · exact S 11 89 3 (by decide +kernel)
 · exact S 11 89 4 (by decide +kernel)
 · exact S 11 89 5 (by decide +kernel)
theorem q11_90:ThresholdAt 11 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 90 0 (by decide +kernel)
 · exact S 11 90 1 (by decide +kernel)
 · exact S 11 90 2 (by decide +kernel)
 · exact S 11 90 3 (by decide +kernel)
 · exact S 11 90 4 (by decide +kernel)
 · exact S 11 90 5 (by decide +kernel)
theorem q11_91:ThresholdAt 11 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 91 0 (by decide +kernel)
 · exact S 11 91 1 (by decide +kernel)
 · exact S 11 91 2 (by decide +kernel)
 · exact S 11 91 3 (by decide +kernel)
 · exact S 11 91 4 (by decide +kernel)
 · exact S 11 91 5 (by decide +kernel)
theorem q11_92:ThresholdAt 11 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 92 0 (by decide +kernel)
 · exact S 11 92 1 (by decide +kernel)
 · exact S 11 92 2 (by decide +kernel)
 · exact S 11 92 3 (by decide +kernel)
 · exact S 11 92 4 (by decide +kernel)
 · exact S 11 92 5 (by decide +kernel)
theorem q11_93:ThresholdAt 11 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 93 0 (by decide +kernel)
 · exact S 11 93 1 (by decide +kernel)
 · exact S 11 93 2 (by decide +kernel)
 · exact S 11 93 3 (by decide +kernel)
 · exact S 11 93 4 (by decide +kernel)
 · exact S 11 93 5 (by decide +kernel)
theorem q11_94:ThresholdAt 11 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 94 0 (by decide +kernel)
 · exact S 11 94 1 (by decide +kernel)
 · exact S 11 94 2 (by decide +kernel)
 · exact S 11 94 3 (by decide +kernel)
 · exact S 11 94 4 (by decide +kernel)
 · exact S 11 94 5 (by decide +kernel)
theorem q11_95:ThresholdAt 11 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 95 0 (by decide +kernel)
 · exact S 11 95 1 (by decide +kernel)
 · exact S 11 95 2 (by decide +kernel)
 · exact S 11 95 3 (by decide +kernel)
 · exact S 11 95 4 (by decide +kernel)
 · exact S 11 95 5 (by decide +kernel)
theorem q11_96:ThresholdAt 11 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 96 0 (by decide +kernel)
 · exact S 11 96 1 (by decide +kernel)
 · exact S 11 96 2 (by decide +kernel)
 · exact S 11 96 3 (by decide +kernel)
 · exact S 11 96 4 (by decide +kernel)
 · exact S 11 96 5 (by decide +kernel)
theorem q11_97:ThresholdAt 11 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 97 0 (by decide +kernel)
 · exact S 11 97 1 (by decide +kernel)
 · exact S 11 97 2 (by decide +kernel)
 · exact S 11 97 3 (by decide +kernel)
 · exact S 11 97 4 (by decide +kernel)
 · exact S 11 97 5 (by decide +kernel)
theorem q11_98:ThresholdAt 11 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 98 0 (by decide +kernel)
 · exact S 11 98 1 (by decide +kernel)
 · exact S 11 98 2 (by decide +kernel)
 · exact S 11 98 3 (by decide +kernel)
 · exact S 11 98 4 (by decide +kernel)
 · exact S 11 98 5 (by decide +kernel)
theorem q11_99:ThresholdAt 11 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 99 0 (by decide +kernel)
 · exact S 11 99 1 (by decide +kernel)
 · exact S 11 99 2 (by decide +kernel)
 · exact S 11 99 3 (by decide +kernel)
 · exact S 11 99 4 (by decide +kernel)
 · exact S 11 99 5 (by decide +kernel)
theorem q11_100:ThresholdAt 11 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 100 0 (by decide +kernel)
 · exact S 11 100 1 (by decide +kernel)
 · exact S 11 100 2 (by decide +kernel)
 · exact S 11 100 3 (by decide +kernel)
 · exact S 11 100 4 (by decide +kernel)
 · exact S 11 100 5 (by decide +kernel)
theorem q11_101:ThresholdAt 11 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 101 0 (by decide +kernel)
 · exact S 11 101 1 (by decide +kernel)
 · exact S 11 101 2 (by decide +kernel)
 · exact S 11 101 3 (by decide +kernel)
 · exact S 11 101 4 (by decide +kernel)
 · exact S 11 101 5 (by decide +kernel)
theorem q11_102:ThresholdAt 11 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 102 0 (by decide +kernel)
 · exact S 11 102 1 (by decide +kernel)
 · exact S 11 102 2 (by decide +kernel)
 · exact S 11 102 3 (by decide +kernel)
 · exact S 11 102 4 (by decide +kernel)
 · exact S 11 102 5 (by decide +kernel)
theorem q11_103:ThresholdAt 11 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 103 0 (by decide +kernel)
 · exact S 11 103 1 (by decide +kernel)
 · exact S 11 103 2 (by decide +kernel)
 · exact S 11 103 3 (by decide +kernel)
 · exact S 11 103 4 (by decide +kernel)
 · exact S 11 103 5 (by decide +kernel)
theorem q11_104:ThresholdAt 11 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 104 0 (by decide +kernel)
 · exact S 11 104 1 (by decide +kernel)
 · exact S 11 104 2 (by decide +kernel)
 · exact S 11 104 3 (by decide +kernel)
 · exact S 11 104 4 (by decide +kernel)
 · exact S 11 104 5 (by decide +kernel)
theorem q11_105:ThresholdAt 11 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 105 0 (by decide +kernel)
 · exact S 11 105 1 (by decide +kernel)
 · exact S 11 105 2 (by decide +kernel)
 · exact S 11 105 3 (by decide +kernel)
 · exact S 11 105 4 (by decide +kernel)
 · exact S 11 105 5 (by decide +kernel)
theorem q11_106:ThresholdAt 11 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 106 0 (by decide +kernel)
 · exact S 11 106 1 (by decide +kernel)
 · exact S 11 106 2 (by decide +kernel)
 · exact S 11 106 3 (by decide +kernel)
 · exact S 11 106 4 (by decide +kernel)
 · exact S 11 106 5 (by decide +kernel)
theorem q11_107:ThresholdAt 11 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 107 0 (by decide +kernel)
 · exact S 11 107 1 (by decide +kernel)
 · exact S 11 107 2 (by decide +kernel)
 · exact S 11 107 3 (by decide +kernel)
 · exact S 11 107 4 (by decide +kernel)
 · exact S 11 107 5 (by decide +kernel)
theorem q11_108:ThresholdAt 11 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 108 0 (by decide +kernel)
 · exact S 11 108 1 (by decide +kernel)
 · exact S 11 108 2 (by decide +kernel)
 · exact S 11 108 3 (by decide +kernel)
 · exact S 11 108 4 (by decide +kernel)
 · exact S 11 108 5 (by decide +kernel)
theorem q11_109:ThresholdAt 11 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 109 0 (by decide +kernel)
 · exact S 11 109 1 (by decide +kernel)
 · exact S 11 109 2 (by decide +kernel)
 · exact S 11 109 3 (by decide +kernel)
 · exact S 11 109 4 (by decide +kernel)
 · exact S 11 109 5 (by decide +kernel)
theorem q11_110:ThresholdAt 11 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 110 0 (by decide +kernel)
 · exact S 11 110 1 (by decide +kernel)
 · exact S 11 110 2 (by decide +kernel)
 · exact S 11 110 3 (by decide +kernel)
 · exact S 11 110 4 (by decide +kernel)
 · exact S 11 110 5 (by decide +kernel)
theorem q11_111:ThresholdAt 11 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 111 0 (by decide +kernel)
 · exact S 11 111 1 (by decide +kernel)
 · exact S 11 111 2 (by decide +kernel)
 · exact S 11 111 3 (by decide +kernel)
 · exact S 11 111 4 (by decide +kernel)
 · exact S 11 111 5 (by decide +kernel)
theorem q11_112:ThresholdAt 11 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 112 0 (by decide +kernel)
 · exact S 11 112 1 (by decide +kernel)
 · exact S 11 112 2 (by decide +kernel)
 · exact S 11 112 3 (by decide +kernel)
 · exact S 11 112 4 (by decide +kernel)
 · exact S 11 112 5 (by decide +kernel)
theorem q11_113:ThresholdAt 11 113:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 113 0 (by decide +kernel)
 · exact S 11 113 1 (by decide +kernel)
 · exact S 11 113 2 (by decide +kernel)
 · exact S 11 113 3 (by decide +kernel)
 · exact S 11 113 4 (by decide +kernel)
 · exact S 11 113 5 (by decide +kernel)
theorem q11_114:ThresholdAt 11 114:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 114 0 (by decide +kernel)
 · exact S 11 114 1 (by decide +kernel)
 · exact S 11 114 2 (by decide +kernel)
 · exact S 11 114 3 (by decide +kernel)
 · exact S 11 114 4 (by decide +kernel)
 · exact S 11 114 5 (by decide +kernel)
theorem q11_115:ThresholdAt 11 115:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 115 0 (by decide +kernel)
 · exact S 11 115 1 (by decide +kernel)
 · exact S 11 115 2 (by decide +kernel)
 · exact S 11 115 3 (by decide +kernel)
 · exact S 11 115 4 (by decide +kernel)
 · exact S 11 115 5 (by decide +kernel)
theorem q11_116:ThresholdAt 11 116:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 116 0 (by decide +kernel)
 · exact S 11 116 1 (by decide +kernel)
 · exact S 11 116 2 (by decide +kernel)
 · exact S 11 116 3 (by decide +kernel)
 · exact S 11 116 4 (by decide +kernel)
 · exact S 11 116 5 (by decide +kernel)
theorem q11_117:ThresholdAt 11 117:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 117 0 (by decide +kernel)
 · exact S 11 117 1 (by decide +kernel)
 · exact S 11 117 2 (by decide +kernel)
 · exact S 11 117 3 (by decide +kernel)
 · exact S 11 117 4 (by decide +kernel)
 · exact S 11 117 5 (by decide +kernel)
theorem q11_118:ThresholdAt 11 118:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 118 0 (by decide +kernel)
 · exact S 11 118 1 (by decide +kernel)
 · exact S 11 118 2 (by decide +kernel)
 · exact S 11 118 3 (by decide +kernel)
 · exact S 11 118 4 (by decide +kernel)
 · exact S 11 118 5 (by decide +kernel)
theorem q11_119:ThresholdAt 11 119:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 119 0 (by decide +kernel)
 · exact S 11 119 1 (by decide +kernel)
 · exact S 11 119 2 (by decide +kernel)
 · exact S 11 119 3 (by decide +kernel)
 · exact S 11 119 4 (by decide +kernel)
 · exact S 11 119 5 (by decide +kernel)
theorem q11_120:ThresholdAt 11 120:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 120 0 (by decide +kernel)
 · exact S 11 120 1 (by decide +kernel)
 · exact S 11 120 2 (by decide +kernel)
 · exact S 11 120 3 (by decide +kernel)
 · exact S 11 120 4 (by decide +kernel)
 · exact S 11 120 5 (by decide +kernel)
theorem q11_121:ThresholdAt 11 121:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 121 0 (by decide +kernel)
 · exact S 11 121 1 (by decide +kernel)
 · exact S 11 121 2 (by decide +kernel)
 · exact S 11 121 3 (by decide +kernel)
 · exact S 11 121 4 (by decide +kernel)
 · exact S 11 121 5 (by decide +kernel)
theorem q11_122:ThresholdAt 11 122:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 122 0 (by decide +kernel)
 · exact S 11 122 1 (by decide +kernel)
 · exact S 11 122 2 (by decide +kernel)
 · exact S 11 122 3 (by decide +kernel)
 · exact S 11 122 4 (by decide +kernel)
 · exact S 11 122 5 (by decide +kernel)
theorem q11_123:ThresholdAt 11 123:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 123 0 (by decide +kernel)
 · exact S 11 123 1 (by decide +kernel)
 · exact S 11 123 2 (by decide +kernel)
 · exact S 11 123 3 (by decide +kernel)
 · exact S 11 123 4 (by decide +kernel)
 · exact S 11 123 5 (by decide +kernel)
theorem q11_124:ThresholdAt 11 124:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 124 0 (by decide +kernel)
 · exact S 11 124 1 (by decide +kernel)
 · exact S 11 124 2 (by decide +kernel)
 · exact S 11 124 3 (by decide +kernel)
 · exact S 11 124 4 (by decide +kernel)
 · exact S 11 124 5 (by decide +kernel)
theorem q11_125:ThresholdAt 11 125:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 125 0 (by decide +kernel)
 · exact S 11 125 1 (by decide +kernel)
 · exact S 11 125 2 (by decide +kernel)
 · exact S 11 125 3 (by decide +kernel)
 · exact S 11 125 4 (by decide +kernel)
 · exact S 11 125 5 (by decide +kernel)
theorem q11_126:ThresholdAt 11 126:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 126 0 (by decide +kernel)
 · exact S 11 126 1 (by decide +kernel)
 · exact S 11 126 2 (by decide +kernel)
 · exact S 11 126 3 (by decide +kernel)
 · exact S 11 126 4 (by decide +kernel)
 · exact S 11 126 5 (by decide +kernel)
theorem q11_127:ThresholdAt 11 127:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 127 0 (by decide +kernel)
 · exact S 11 127 1 (by decide +kernel)
 · exact S 11 127 2 (by decide +kernel)
 · exact S 11 127 3 (by decide +kernel)
 · exact S 11 127 4 (by decide +kernel)
 · exact S 11 127 5 (by decide +kernel)
theorem q11_128:ThresholdAt 11 128:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 128 0 (by decide +kernel)
 · exact S 11 128 1 (by decide +kernel)
 · exact S 11 128 2 (by decide +kernel)
 · exact S 11 128 3 (by decide +kernel)
 · exact S 11 128 4 (by decide +kernel)
 · exact S 11 128 5 (by decide +kernel)
theorem q11_129:ThresholdAt 11 129:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 129 0 (by decide +kernel)
 · exact S 11 129 1 (by decide +kernel)
 · exact S 11 129 2 (by decide +kernel)
 · exact S 11 129 3 (by decide +kernel)
 · exact S 11 129 4 (by decide +kernel)
 · exact S 11 129 5 (by decide +kernel)
theorem q11_130:ThresholdAt 11 130:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 130 0 (by decide +kernel)
 · exact S 11 130 1 (by decide +kernel)
 · exact S 11 130 2 (by decide +kernel)
 · exact S 11 130 3 (by decide +kernel)
 · exact S 11 130 4 (by decide +kernel)
 · exact S 11 130 5 (by decide +kernel)
theorem q11_131:ThresholdAt 11 131:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 11 131 0 (by decide +kernel)
 · exact S 11 131 1 (by decide +kernel)
 · exact S 11 131 2 (by decide +kernel)
 · exact S 11 131 3 (by decide +kernel)
 · exact S 11 131 4 (by decide +kernel)
 · exact S 11 131 5 (by decide +kernel)
theorem checkedR11:∀ V ∈ List.range 132,ThresholdAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0_132:V < 66
  · by_cases h0_66:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have he:V = 0:=by omega
                subst V
                exact q11_0
              · have he:V = 1:=by omega
                subst V
                exact q11_1
            · by_cases h2_4:V < 3
              · have he:V = 2:=by omega
                subst V
                exact q11_2
              · have he:V = 3:=by omega
                subst V
                exact q11_3
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have he:V = 4:=by omega
                subst V
                exact q11_4
              · have he:V = 5:=by omega
                subst V
                exact q11_5
            · by_cases h6_8:V < 7
              · have he:V = 6:=by omega
                subst V
                exact q11_6
              · have he:V = 7:=by omega
                subst V
                exact q11_7
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q11_8
              · have he:V = 9:=by omega
                subst V
                exact q11_9
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q11_10
              · have he:V = 11:=by omega
                subst V
                exact q11_11
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q11_12
              · have he:V = 13:=by omega
                subst V
                exact q11_13
            · by_cases h14_16:V < 15
              · have he:V = 14:=by omega
                subst V
                exact q11_14
              · have he:V = 15:=by omega
                subst V
                exact q11_15
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have he:V = 16:=by omega
                subst V
                exact q11_16
              · have he:V = 17:=by omega
                subst V
                exact q11_17
            · by_cases h18_20:V < 19
              · have he:V = 18:=by omega
                subst V
                exact q11_18
              · have he:V = 19:=by omega
                subst V
                exact q11_19
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have he:V = 20:=by omega
                subst V
                exact q11_20
              · have he:V = 21:=by omega
                subst V
                exact q11_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q11_22
              · have he:V = 23:=by omega
                subst V
                exact q11_23
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q11_24
              · have he:V = 25:=by omega
                subst V
                exact q11_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q11_26
              · have he:V = 27:=by omega
                subst V
                exact q11_27
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have he:V = 28:=by omega
                subst V
                exact q11_28
              · have he:V = 29:=by omega
                subst V
                exact q11_29
            · by_cases h30_33:V < 31
              · have he:V = 30:=by omega
                subst V
                exact q11_30
              · by_cases h31_33:V < 32
                · have he:V = 31:=by omega
                  subst V
                  exact q11_31
                · have he:V = 32:=by omega
                  subst V
                  exact q11_32
    · by_cases h33_66:V < 49
      · by_cases h33_49:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q11_33
              · have he:V = 34:=by omega
                subst V
                exact q11_34
            · by_cases h35_37:V < 36
              · have he:V = 35:=by omega
                subst V
                exact q11_35
              · have he:V = 36:=by omega
                subst V
                exact q11_36
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have he:V = 37:=by omega
                subst V
                exact q11_37
              · have he:V = 38:=by omega
                subst V
                exact q11_38
            · by_cases h39_41:V < 40
              · have he:V = 39:=by omega
                subst V
                exact q11_39
              · have he:V = 40:=by omega
                subst V
                exact q11_40
        · by_cases h41_49:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have he:V = 41:=by omega
                subst V
                exact q11_41
              · have he:V = 42:=by omega
                subst V
                exact q11_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q11_43
              · have he:V = 44:=by omega
                subst V
                exact q11_44
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q11_45
              · have he:V = 46:=by omega
                subst V
                exact q11_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q11_47
              · have he:V = 48:=by omega
                subst V
                exact q11_48
      · by_cases h49_66:V < 57
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have he:V = 49:=by omega
                subst V
                exact q11_49
              · have he:V = 50:=by omega
                subst V
                exact q11_50
            · by_cases h51_53:V < 52
              · have he:V = 51:=by omega
                subst V
                exact q11_51
              · have he:V = 52:=by omega
                subst V
                exact q11_52
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have he:V = 53:=by omega
                subst V
                exact q11_53
              · have he:V = 54:=by omega
                subst V
                exact q11_54
            · by_cases h55_57:V < 56
              · have he:V = 55:=by omega
                subst V
                exact q11_55
              · have he:V = 56:=by omega
                subst V
                exact q11_56
        · by_cases h57_66:V < 61
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q11_57
              · have he:V = 58:=by omega
                subst V
                exact q11_58
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q11_59
              · have he:V = 60:=by omega
                subst V
                exact q11_60
          · by_cases h61_66:V < 63
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q11_61
              · have he:V = 62:=by omega
                subst V
                exact q11_62
            · by_cases h63_66:V < 64
              · have he:V = 63:=by omega
                subst V
                exact q11_63
              · by_cases h64_66:V < 65
                · have he:V = 64:=by omega
                  subst V
                  exact q11_64
                · have he:V = 65:=by omega
                  subst V
                  exact q11_65
  · by_cases h66_132:V < 99
    · by_cases h66_99:V < 82
      · by_cases h66_82:V < 74
        · by_cases h66_74:V < 70
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q11_66
              · have he:V = 67:=by omega
                subst V
                exact q11_67
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q11_68
              · have he:V = 69:=by omega
                subst V
                exact q11_69
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have he:V = 70:=by omega
                subst V
                exact q11_70
              · have he:V = 71:=by omega
                subst V
                exact q11_71
            · by_cases h72_74:V < 73
              · have he:V = 72:=by omega
                subst V
                exact q11_72
              · have he:V = 73:=by omega
                subst V
                exact q11_73
        · by_cases h74_82:V < 78
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have he:V = 74:=by omega
                subst V
                exact q11_74
              · have he:V = 75:=by omega
                subst V
                exact q11_75
            · by_cases h76_78:V < 77
              · have he:V = 76:=by omega
                subst V
                exact q11_76
              · have he:V = 77:=by omega
                subst V
                exact q11_77
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q11_78
              · have he:V = 79:=by omega
                subst V
                exact q11_79
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q11_80
              · have he:V = 81:=by omega
                subst V
                exact q11_81
      · by_cases h82_99:V < 90
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q11_82
              · have he:V = 83:=by omega
                subst V
                exact q11_83
            · by_cases h84_86:V < 85
              · have he:V = 84:=by omega
                subst V
                exact q11_84
              · have he:V = 85:=by omega
                subst V
                exact q11_85
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have he:V = 86:=by omega
                subst V
                exact q11_86
              · have he:V = 87:=by omega
                subst V
                exact q11_87
            · by_cases h88_90:V < 89
              · have he:V = 88:=by omega
                subst V
                exact q11_88
              · have he:V = 89:=by omega
                subst V
                exact q11_89
        · by_cases h90_99:V < 94
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have he:V = 90:=by omega
                subst V
                exact q11_90
              · have he:V = 91:=by omega
                subst V
                exact q11_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q11_92
              · have he:V = 93:=by omega
                subst V
                exact q11_93
          · by_cases h94_99:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q11_94
              · have he:V = 95:=by omega
                subst V
                exact q11_95
            · by_cases h96_99:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q11_96
              · by_cases h97_99:V < 98
                · have he:V = 97:=by omega
                  subst V
                  exact q11_97
                · have he:V = 98:=by omega
                  subst V
                  exact q11_98
    · by_cases h99_132:V < 115
      · by_cases h99_115:V < 107
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q11_99
              · have he:V = 100:=by omega
                subst V
                exact q11_100
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q11_101
              · have he:V = 102:=by omega
                subst V
                exact q11_102
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q11_103
              · have he:V = 104:=by omega
                subst V
                exact q11_104
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q11_105
              · have he:V = 106:=by omega
                subst V
                exact q11_106
        · by_cases h107_115:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q11_107
              · have he:V = 108:=by omega
                subst V
                exact q11_108
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q11_109
              · have he:V = 110:=by omega
                subst V
                exact q11_110
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q11_111
              · have he:V = 112:=by omega
                subst V
                exact q11_112
            · by_cases h113_115:V < 114
              · have he:V = 113:=by omega
                subst V
                exact q11_113
              · have he:V = 114:=by omega
                subst V
                exact q11_114
      · by_cases h115_132:V < 123
        · by_cases h115_123:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have he:V = 115:=by omega
                subst V
                exact q11_115
              · have he:V = 116:=by omega
                subst V
                exact q11_116
            · by_cases h117_119:V < 118
              · have he:V = 117:=by omega
                subst V
                exact q11_117
              · have he:V = 118:=by omega
                subst V
                exact q11_118
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have he:V = 119:=by omega
                subst V
                exact q11_119
              · have he:V = 120:=by omega
                subst V
                exact q11_120
            · by_cases h121_123:V < 122
              · have he:V = 121:=by omega
                subst V
                exact q11_121
              · have he:V = 122:=by omega
                subst V
                exact q11_122
        · by_cases h123_132:V < 127
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have he:V = 123:=by omega
                subst V
                exact q11_123
              · have he:V = 124:=by omega
                subst V
                exact q11_124
            · by_cases h125_127:V < 126
              · have he:V = 125:=by omega
                subst V
                exact q11_125
              · have he:V = 126:=by omega
                subst V
                exact q11_126
          · by_cases h127_132:V < 129
            · by_cases h127_129:V < 128
              · have he:V = 127:=by omega
                subst V
                exact q11_127
              · have he:V = 128:=by omega
                subst V
                exact q11_128
            · by_cases h129_132:V < 130
              · have he:V = 129:=by omega
                subst V
                exact q11_129
              · by_cases h130_132:V < 131
                · have he:V = 130:=by omega
                  subst V
                  exact q11_130
                · have he:V = 131:=by omega
                  subst V
                  exact q11_131
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
