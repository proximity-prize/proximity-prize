import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked29

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem q30_0:ThresholdAt 30 0:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 0 0 (by decide +kernel)
 · exact S 30 0 1 (by decide +kernel)
 · exact S 30 0 2 (by decide +kernel)
 · exact S 30 0 3 (by decide +kernel)
 · exact S 30 0 4 (by decide +kernel)
 · exact S 30 0 5 (by decide +kernel)
theorem q30_1:ThresholdAt 30 1:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 1 0 (by decide +kernel)
 · exact S 30 1 1 (by decide +kernel)
 · exact S 30 1 2 (by decide +kernel)
 · exact S 30 1 3 (by decide +kernel)
 · exact S 30 1 4 (by decide +kernel)
 · exact S 30 1 5 (by decide +kernel)
theorem q30_2:ThresholdAt 30 2:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 2 0 (by decide +kernel)
 · exact S 30 2 1 (by decide +kernel)
 · exact S 30 2 2 (by decide +kernel)
 · exact S 30 2 3 (by decide +kernel)
 · exact S 30 2 4 (by decide +kernel)
 · exact S 30 2 5 (by decide +kernel)
theorem q30_3:ThresholdAt 30 3:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 3 0 (by decide +kernel)
 · exact S 30 3 1 (by decide +kernel)
 · exact S 30 3 2 (by decide +kernel)
 · exact S 30 3 3 (by decide +kernel)
 · exact S 30 3 4 (by decide +kernel)
 · exact S 30 3 5 (by decide +kernel)
theorem q30_4:ThresholdAt 30 4:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 4 0 (by decide +kernel)
 · exact S 30 4 1 (by decide +kernel)
 · exact S 30 4 2 (by decide +kernel)
 · exact S 30 4 3 (by decide +kernel)
 · exact S 30 4 4 (by decide +kernel)
 · exact S 30 4 5 (by decide +kernel)
theorem q30_5:ThresholdAt 30 5:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 5 0 (by decide +kernel)
 · exact S 30 5 1 (by decide +kernel)
 · exact S 30 5 2 (by decide +kernel)
 · exact S 30 5 3 (by decide +kernel)
 · exact S 30 5 4 (by decide +kernel)
 · exact S 30 5 5 (by decide +kernel)
theorem q30_6:ThresholdAt 30 6:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 6 0 (by decide +kernel)
 · exact S 30 6 1 (by decide +kernel)
 · exact S 30 6 2 (by decide +kernel)
 · exact S 30 6 3 (by decide +kernel)
 · exact S 30 6 4 (by decide +kernel)
 · exact S 30 6 5 (by decide +kernel)
theorem q30_7:ThresholdAt 30 7:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 7 0 (by decide +kernel)
 · exact S 30 7 1 (by decide +kernel)
 · exact S 30 7 2 (by decide +kernel)
 · exact S 30 7 3 (by decide +kernel)
 · exact S 30 7 4 (by decide +kernel)
 · exact S 30 7 5 (by decide +kernel)
theorem q30_8:ThresholdAt 30 8:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 8 0 (by decide +kernel)
 · exact S 30 8 1 (by decide +kernel)
 · exact S 30 8 2 (by decide +kernel)
 · exact S 30 8 3 (by decide +kernel)
 · exact S 30 8 4 (by decide +kernel)
 · exact S 30 8 5 (by decide +kernel)
theorem q30_9:ThresholdAt 30 9:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 9 0 (by decide +kernel)
 · exact S 30 9 1 (by decide +kernel)
 · exact S 30 9 2 (by decide +kernel)
 · exact S 30 9 3 (by decide +kernel)
 · exact S 30 9 4 (by decide +kernel)
 · exact S 30 9 5 (by decide +kernel)
theorem q30_10:ThresholdAt 30 10:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 10 0 (by decide +kernel)
 · exact S 30 10 1 (by decide +kernel)
 · exact S 30 10 2 (by decide +kernel)
 · exact S 30 10 3 (by decide +kernel)
 · exact S 30 10 4 (by decide +kernel)
 · exact S 30 10 5 (by decide +kernel)
theorem q30_11:ThresholdAt 30 11:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 11 0 (by decide +kernel)
 · exact S 30 11 1 (by decide +kernel)
 · exact S 30 11 2 (by decide +kernel)
 · exact S 30 11 3 (by decide +kernel)
 · exact S 30 11 4 (by decide +kernel)
 · exact S 30 11 5 (by decide +kernel)
theorem q30_12:ThresholdAt 30 12:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 12 0 (by decide +kernel)
 · exact S 30 12 1 (by decide +kernel)
 · exact S 30 12 2 (by decide +kernel)
 · exact S 30 12 3 (by decide +kernel)
 · exact S 30 12 4 (by decide +kernel)
 · exact S 30 12 5 (by decide +kernel)
theorem q30_13:ThresholdAt 30 13:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 13 0 (by decide +kernel)
 · exact S 30 13 1 (by decide +kernel)
 · exact S 30 13 2 (by decide +kernel)
 · exact S 30 13 3 (by decide +kernel)
 · exact S 30 13 4 (by decide +kernel)
 · exact S 30 13 5 (by decide +kernel)
theorem q30_14:ThresholdAt 30 14:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 14 0 (by decide +kernel)
 · exact S 30 14 1 (by decide +kernel)
 · exact S 30 14 2 (by decide +kernel)
 · exact S 30 14 3 (by decide +kernel)
 · exact S 30 14 4 (by decide +kernel)
 · exact S 30 14 5 (by decide +kernel)
theorem q30_15:ThresholdAt 30 15:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 15 0 (by decide +kernel)
 · exact S 30 15 1 (by decide +kernel)
 · exact S 30 15 2 (by decide +kernel)
 · exact S 30 15 3 (by decide +kernel)
 · exact S 30 15 4 (by decide +kernel)
 · exact S 30 15 5 (by decide +kernel)
theorem q30_16:ThresholdAt 30 16:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 16 0 (by decide +kernel)
 · exact S 30 16 1 (by decide +kernel)
 · exact S 30 16 2 (by decide +kernel)
 · exact S 30 16 3 (by decide +kernel)
 · exact S 30 16 4 (by decide +kernel)
 · exact S 30 16 5 (by decide +kernel)
theorem q30_17:ThresholdAt 30 17:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 17 0 (by decide +kernel)
 · exact S 30 17 1 (by decide +kernel)
 · exact S 30 17 2 (by decide +kernel)
 · exact S 30 17 3 (by decide +kernel)
 · exact S 30 17 4 (by decide +kernel)
 · exact S 30 17 5 (by decide +kernel)
theorem q30_18:ThresholdAt 30 18:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 18 0 (by decide +kernel)
 · exact S 30 18 1 (by decide +kernel)
 · exact S 30 18 2 (by decide +kernel)
 · exact S 30 18 3 (by decide +kernel)
 · exact S 30 18 4 (by decide +kernel)
 · exact S 30 18 5 (by decide +kernel)
theorem q30_19:ThresholdAt 30 19:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 19 0 (by decide +kernel)
 · exact S 30 19 1 (by decide +kernel)
 · exact S 30 19 2 (by decide +kernel)
 · exact S 30 19 3 (by decide +kernel)
 · exact S 30 19 4 (by decide +kernel)
 · exact S 30 19 5 (by decide +kernel)
theorem q30_20:ThresholdAt 30 20:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 20 0 (by decide +kernel)
 · exact S 30 20 1 (by decide +kernel)
 · exact S 30 20 2 (by decide +kernel)
 · exact S 30 20 3 (by decide +kernel)
 · exact S 30 20 4 (by decide +kernel)
 · exact S 30 20 5 (by decide +kernel)
theorem q30_21:ThresholdAt 30 21:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 21 0 (by decide +kernel)
 · exact S 30 21 1 (by decide +kernel)
 · exact S 30 21 2 (by decide +kernel)
 · exact S 30 21 3 (by decide +kernel)
 · exact S 30 21 4 (by decide +kernel)
 · exact S 30 21 5 (by decide +kernel)
theorem q30_22:ThresholdAt 30 22:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 22 0 (by decide +kernel)
 · exact S 30 22 1 (by decide +kernel)
 · exact S 30 22 2 (by decide +kernel)
 · exact S 30 22 3 (by decide +kernel)
 · exact S 30 22 4 (by decide +kernel)
 · exact S 30 22 5 (by decide +kernel)
theorem q30_23:ThresholdAt 30 23:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 23 0 (by decide +kernel)
 · exact S 30 23 1 (by decide +kernel)
 · exact S 30 23 2 (by decide +kernel)
 · exact S 30 23 3 (by decide +kernel)
 · exact S 30 23 4 (by decide +kernel)
 · exact S 30 23 5 (by decide +kernel)
theorem q30_24:ThresholdAt 30 24:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 24 0 (by decide +kernel)
 · exact S 30 24 1 (by decide +kernel)
 · exact S 30 24 2 (by decide +kernel)
 · exact S 30 24 3 (by decide +kernel)
 · exact S 30 24 4 (by decide +kernel)
 · exact S 30 24 5 (by decide +kernel)
theorem q30_25:ThresholdAt 30 25:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 25 0 (by decide +kernel)
 · exact S 30 25 1 (by decide +kernel)
 · exact S 30 25 2 (by decide +kernel)
 · exact S 30 25 3 (by decide +kernel)
 · exact S 30 25 4 (by decide +kernel)
 · exact S 30 25 5 (by decide +kernel)
theorem q30_26:ThresholdAt 30 26:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 26 0 (by decide +kernel)
 · exact S 30 26 1 (by decide +kernel)
 · exact S 30 26 2 (by decide +kernel)
 · exact S 30 26 3 (by decide +kernel)
 · exact S 30 26 4 (by decide +kernel)
 · exact S 30 26 5 (by decide +kernel)
theorem q30_27:ThresholdAt 30 27:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 27 0 (by decide +kernel)
 · exact S 30 27 1 (by decide +kernel)
 · exact S 30 27 2 (by decide +kernel)
 · exact S 30 27 3 (by decide +kernel)
 · exact S 30 27 4 (by decide +kernel)
 · exact S 30 27 5 (by decide +kernel)
theorem q30_28:ThresholdAt 30 28:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 28 0 (by decide +kernel)
 · exact S 30 28 1 (by decide +kernel)
 · exact S 30 28 2 (by decide +kernel)
 · exact S 30 28 3 (by decide +kernel)
 · exact S 30 28 4 (by decide +kernel)
 · exact S 30 28 5 (by decide +kernel)
theorem q30_29:ThresholdAt 30 29:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 29 0 (by decide +kernel)
 · exact S 30 29 1 (by decide +kernel)
 · exact S 30 29 2 (by decide +kernel)
 · exact S 30 29 3 (by decide +kernel)
 · exact S 30 29 4 (by decide +kernel)
 · exact S 30 29 5 (by decide +kernel)
theorem q30_30:ThresholdAt 30 30:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 30 0 (by decide +kernel)
 · exact S 30 30 1 (by decide +kernel)
 · exact S 30 30 2 (by decide +kernel)
 · exact S 30 30 3 (by decide +kernel)
 · exact S 30 30 4 (by decide +kernel)
 · exact S 30 30 5 (by decide +kernel)
theorem q30_31:ThresholdAt 30 31:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 31 0 (by decide +kernel)
 · exact S 30 31 1 (by decide +kernel)
 · exact S 30 31 2 (by decide +kernel)
 · exact S 30 31 3 (by decide +kernel)
 · exact S 30 31 4 (by decide +kernel)
 · exact S 30 31 5 (by decide +kernel)
theorem q30_32:ThresholdAt 30 32:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 32 0 (by decide +kernel)
 · exact S 30 32 1 (by decide +kernel)
 · exact S 30 32 2 (by decide +kernel)
 · exact S 30 32 3 (by decide +kernel)
 · exact S 30 32 4 (by decide +kernel)
 · exact S 30 32 5 (by decide +kernel)
theorem q30_33:ThresholdAt 30 33:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 33 0 (by decide +kernel)
 · exact S 30 33 1 (by decide +kernel)
 · exact S 30 33 2 (by decide +kernel)
 · exact S 30 33 3 (by decide +kernel)
 · exact S 30 33 4 (by decide +kernel)
 · exact S 30 33 5 (by decide +kernel)
theorem q30_34:ThresholdAt 30 34:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 34 0 (by decide +kernel)
 · exact S 30 34 1 (by decide +kernel)
 · exact S 30 34 2 (by decide +kernel)
 · exact S 30 34 3 (by decide +kernel)
 · exact S 30 34 4 (by decide +kernel)
 · exact S 30 34 5 (by decide +kernel)
theorem q30_35:ThresholdAt 30 35:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 35 0 (by decide +kernel)
 · exact S 30 35 1 (by decide +kernel)
 · exact S 30 35 2 (by decide +kernel)
 · exact S 30 35 3 (by decide +kernel)
 · exact S 30 35 4 (by decide +kernel)
 · exact S 30 35 5 (by decide +kernel)
theorem q30_36:ThresholdAt 30 36:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 36 0 (by decide +kernel)
 · exact S 30 36 1 (by decide +kernel)
 · exact S 30 36 2 (by decide +kernel)
 · exact S 30 36 3 (by decide +kernel)
 · exact S 30 36 4 (by decide +kernel)
 · exact S 30 36 5 (by decide +kernel)
theorem q30_37:ThresholdAt 30 37:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 37 0 (by decide +kernel)
 · exact S 30 37 1 (by decide +kernel)
 · exact S 30 37 2 (by decide +kernel)
 · exact S 30 37 3 (by decide +kernel)
 · exact S 30 37 4 (by decide +kernel)
 · exact S 30 37 5 (by decide +kernel)
theorem q30_38:ThresholdAt 30 38:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 38 0 (by decide +kernel)
 · exact S 30 38 1 (by decide +kernel)
 · exact S 30 38 2 (by decide +kernel)
 · exact S 30 38 3 (by decide +kernel)
 · exact S 30 38 4 (by decide +kernel)
 · exact S 30 38 5 (by decide +kernel)
theorem q30_39:ThresholdAt 30 39:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 39 0 (by decide +kernel)
 · exact S 30 39 1 (by decide +kernel)
 · exact S 30 39 2 (by decide +kernel)
 · exact S 30 39 3 (by decide +kernel)
 · exact S 30 39 4 (by decide +kernel)
 · exact S 30 39 5 (by decide +kernel)
theorem q30_40:ThresholdAt 30 40:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 40 0 (by decide +kernel)
 · exact S 30 40 1 (by decide +kernel)
 · exact S 30 40 2 (by decide +kernel)
 · exact S 30 40 3 (by decide +kernel)
 · exact S 30 40 4 (by decide +kernel)
 · exact S 30 40 5 (by decide +kernel)
theorem q30_41:ThresholdAt 30 41:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 41 0 (by decide +kernel)
 · exact S 30 41 1 (by decide +kernel)
 · exact S 30 41 2 (by decide +kernel)
 · exact S 30 41 3 (by decide +kernel)
 · exact S 30 41 4 (by decide +kernel)
 · exact S 30 41 5 (by decide +kernel)
theorem q30_42:ThresholdAt 30 42:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 42 0 (by decide +kernel)
 · exact S 30 42 1 (by decide +kernel)
 · exact S 30 42 2 (by decide +kernel)
 · exact S 30 42 3 (by decide +kernel)
 · exact S 30 42 4 (by decide +kernel)
 · exact S 30 42 5 (by decide +kernel)
theorem q30_43:ThresholdAt 30 43:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 43 0 (by decide +kernel)
 · exact S 30 43 1 (by decide +kernel)
 · exact S 30 43 2 (by decide +kernel)
 · exact S 30 43 3 (by decide +kernel)
 · exact S 30 43 4 (by decide +kernel)
 · exact S 30 43 5 (by decide +kernel)
theorem q30_44:ThresholdAt 30 44:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 44 0 (by decide +kernel)
 · exact S 30 44 1 (by decide +kernel)
 · exact S 30 44 2 (by decide +kernel)
 · exact S 30 44 3 (by decide +kernel)
 · exact S 30 44 4 (by decide +kernel)
 · exact S 30 44 5 (by decide +kernel)
theorem q30_45:ThresholdAt 30 45:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 45 0 (by decide +kernel)
 · exact S 30 45 1 (by decide +kernel)
 · exact S 30 45 2 (by decide +kernel)
 · exact S 30 45 3 (by decide +kernel)
 · exact S 30 45 4 (by decide +kernel)
 · exact S 30 45 5 (by decide +kernel)
theorem q30_46:ThresholdAt 30 46:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 46 0 (by decide +kernel)
 · exact S 30 46 1 (by decide +kernel)
 · exact S 30 46 2 (by decide +kernel)
 · exact S 30 46 3 (by decide +kernel)
 · exact S 30 46 4 (by decide +kernel)
 · exact S 30 46 5 (by decide +kernel)
theorem q30_47:ThresholdAt 30 47:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 47 0 (by decide +kernel)
 · exact S 30 47 1 (by decide +kernel)
 · exact S 30 47 2 (by decide +kernel)
 · exact S 30 47 3 (by decide +kernel)
 · exact S 30 47 4 (by decide +kernel)
 · exact S 30 47 5 (by decide +kernel)
theorem q30_48:ThresholdAt 30 48:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 48 0 (by decide +kernel)
 · exact S 30 48 1 (by decide +kernel)
 · exact S 30 48 2 (by decide +kernel)
 · exact S 30 48 3 (by decide +kernel)
 · exact S 30 48 4 (by decide +kernel)
 · exact S 30 48 5 (by decide +kernel)
theorem q30_49:ThresholdAt 30 49:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 49 0 (by decide +kernel)
 · exact S 30 49 1 (by decide +kernel)
 · exact S 30 49 2 (by decide +kernel)
 · exact S 30 49 3 (by decide +kernel)
 · exact S 30 49 4 (by decide +kernel)
 · exact S 30 49 5 (by decide +kernel)
theorem q30_50:ThresholdAt 30 50:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 50 0 (by decide +kernel)
 · exact S 30 50 1 (by decide +kernel)
 · exact S 30 50 2 (by decide +kernel)
 · exact S 30 50 3 (by decide +kernel)
 · exact S 30 50 4 (by decide +kernel)
 · exact S 30 50 5 (by decide +kernel)
theorem q30_51:ThresholdAt 30 51:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 51 0 (by decide +kernel)
 · exact S 30 51 1 (by decide +kernel)
 · exact S 30 51 2 (by decide +kernel)
 · exact S 30 51 3 (by decide +kernel)
 · exact S 30 51 4 (by decide +kernel)
 · exact S 30 51 5 (by decide +kernel)
theorem q30_52:ThresholdAt 30 52:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 52 0 (by decide +kernel)
 · exact S 30 52 1 (by decide +kernel)
 · exact S 30 52 2 (by decide +kernel)
 · exact S 30 52 3 (by decide +kernel)
 · exact S 30 52 4 (by decide +kernel)
 · exact S 30 52 5 (by decide +kernel)
theorem q30_53:ThresholdAt 30 53:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 53 0 (by decide +kernel)
 · exact S 30 53 1 (by decide +kernel)
 · exact S 30 53 2 (by decide +kernel)
 · exact S 30 53 3 (by decide +kernel)
 · exact S 30 53 4 (by decide +kernel)
 · exact S 30 53 5 (by decide +kernel)
theorem q30_54:ThresholdAt 30 54:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 54 0 (by decide +kernel)
 · exact S 30 54 1 (by decide +kernel)
 · exact S 30 54 2 (by decide +kernel)
 · exact S 30 54 3 (by decide +kernel)
 · exact S 30 54 4 (by decide +kernel)
 · exact S 30 54 5 (by decide +kernel)
theorem q30_55:ThresholdAt 30 55:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 55 0 (by decide +kernel)
 · exact S 30 55 1 (by decide +kernel)
 · exact S 30 55 2 (by decide +kernel)
 · exact S 30 55 3 (by decide +kernel)
 · exact S 30 55 4 (by decide +kernel)
 · exact S 30 55 5 (by decide +kernel)
theorem q30_56:ThresholdAt 30 56:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 56 0 (by decide +kernel)
 · exact S 30 56 1 (by decide +kernel)
 · exact S 30 56 2 (by decide +kernel)
 · exact S 30 56 3 (by decide +kernel)
 · exact S 30 56 4 (by decide +kernel)
 · exact S 30 56 5 (by decide +kernel)
theorem q30_57:ThresholdAt 30 57:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 57 0 (by decide +kernel)
 · exact S 30 57 1 (by decide +kernel)
 · exact S 30 57 2 (by decide +kernel)
 · exact S 30 57 3 (by decide +kernel)
 · exact S 30 57 4 (by decide +kernel)
 · exact S 30 57 5 (by decide +kernel)
theorem q30_58:ThresholdAt 30 58:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 58 0 (by decide +kernel)
 · exact S 30 58 1 (by decide +kernel)
 · exact S 30 58 2 (by decide +kernel)
 · exact S 30 58 3 (by decide +kernel)
 · exact S 30 58 4 (by decide +kernel)
 · exact S 30 58 5 (by decide +kernel)
theorem q30_59:ThresholdAt 30 59:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 59 0 (by decide +kernel)
 · exact S 30 59 1 (by decide +kernel)
 · exact S 30 59 2 (by decide +kernel)
 · exact S 30 59 3 (by decide +kernel)
 · exact S 30 59 4 (by decide +kernel)
 · exact S 30 59 5 (by decide +kernel)
theorem q30_60:ThresholdAt 30 60:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 60 0 (by decide +kernel)
 · exact S 30 60 1 (by decide +kernel)
 · exact S 30 60 2 (by decide +kernel)
 · exact S 30 60 3 (by decide +kernel)
 · exact S 30 60 4 (by decide +kernel)
 · exact S 30 60 5 (by decide +kernel)
theorem q30_61:ThresholdAt 30 61:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 61 0 (by decide +kernel)
 · exact S 30 61 1 (by decide +kernel)
 · exact S 30 61 2 (by decide +kernel)
 · exact S 30 61 3 (by decide +kernel)
 · exact S 30 61 4 (by decide +kernel)
 · exact S 30 61 5 (by decide +kernel)
theorem q30_62:ThresholdAt 30 62:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 62 0 (by decide +kernel)
 · exact S 30 62 1 (by decide +kernel)
 · exact S 30 62 2 (by decide +kernel)
 · exact S 30 62 3 (by decide +kernel)
 · exact S 30 62 4 (by decide +kernel)
 · exact S 30 62 5 (by decide +kernel)
theorem q30_63:ThresholdAt 30 63:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 63 0 (by decide +kernel)
 · exact S 30 63 1 (by decide +kernel)
 · exact S 30 63 2 (by decide +kernel)
 · exact S 30 63 3 (by decide +kernel)
 · exact S 30 63 4 (by decide +kernel)
 · exact S 30 63 5 (by decide +kernel)
theorem q30_64:ThresholdAt 30 64:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 64 0 (by decide +kernel)
 · exact S 30 64 1 (by decide +kernel)
 · exact S 30 64 2 (by decide +kernel)
 · exact S 30 64 3 (by decide +kernel)
 · exact S 30 64 4 (by decide +kernel)
 · exact S 30 64 5 (by decide +kernel)
theorem q30_65:ThresholdAt 30 65:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 65 0 (by decide +kernel)
 · exact S 30 65 1 (by decide +kernel)
 · exact S 30 65 2 (by decide +kernel)
 · exact S 30 65 3 (by decide +kernel)
 · exact S 30 65 4 (by decide +kernel)
 · exact S 30 65 5 (by decide +kernel)
theorem q30_66:ThresholdAt 30 66:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 66 0 (by decide +kernel)
 · exact S 30 66 1 (by decide +kernel)
 · exact S 30 66 2 (by decide +kernel)
 · exact S 30 66 3 (by decide +kernel)
 · exact S 30 66 4 (by decide +kernel)
 · exact S 30 66 5 (by decide +kernel)
theorem q30_67:ThresholdAt 30 67:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 67 0 (by decide +kernel)
 · exact S 30 67 1 (by decide +kernel)
 · exact S 30 67 2 (by decide +kernel)
 · exact S 30 67 3 (by decide +kernel)
 · exact S 30 67 4 (by decide +kernel)
 · exact S 30 67 5 (by decide +kernel)
theorem q30_68:ThresholdAt 30 68:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 68 0 (by decide +kernel)
 · exact S 30 68 1 (by decide +kernel)
 · exact S 30 68 2 (by decide +kernel)
 · exact S 30 68 3 (by decide +kernel)
 · exact S 30 68 4 (by decide +kernel)
 · exact S 30 68 5 (by decide +kernel)
theorem q30_69:ThresholdAt 30 69:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 69 0 (by decide +kernel)
 · exact S 30 69 1 (by decide +kernel)
 · exact S 30 69 2 (by decide +kernel)
 · exact S 30 69 3 (by decide +kernel)
 · exact S 30 69 4 (by decide +kernel)
 · exact S 30 69 5 (by decide +kernel)
theorem q30_70:ThresholdAt 30 70:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 70 0 (by decide +kernel)
 · exact S 30 70 1 (by decide +kernel)
 · exact S 30 70 2 (by decide +kernel)
 · exact S 30 70 3 (by decide +kernel)
 · exact S 30 70 4 (by decide +kernel)
 · exact S 30 70 5 (by decide +kernel)
theorem q30_71:ThresholdAt 30 71:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 71 0 (by decide +kernel)
 · exact S 30 71 1 (by decide +kernel)
 · exact S 30 71 2 (by decide +kernel)
 · exact S 30 71 3 (by decide +kernel)
 · exact S 30 71 4 (by decide +kernel)
 · exact S 30 71 5 (by decide +kernel)
theorem q30_72:ThresholdAt 30 72:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 72 0 (by decide +kernel)
 · exact S 30 72 1 (by decide +kernel)
 · exact S 30 72 2 (by decide +kernel)
 · exact S 30 72 3 (by decide +kernel)
 · exact S 30 72 4 (by decide +kernel)
 · exact S 30 72 5 (by decide +kernel)
theorem q30_73:ThresholdAt 30 73:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 73 0 (by decide +kernel)
 · exact S 30 73 1 (by decide +kernel)
 · exact S 30 73 2 (by decide +kernel)
 · exact S 30 73 3 (by decide +kernel)
 · exact S 30 73 4 (by decide +kernel)
 · exact S 30 73 5 (by decide +kernel)
theorem q30_74:ThresholdAt 30 74:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 74 0 (by decide +kernel)
 · exact S 30 74 1 (by decide +kernel)
 · exact S 30 74 2 (by decide +kernel)
 · exact S 30 74 3 (by decide +kernel)
 · exact S 30 74 4 (by decide +kernel)
 · exact S 30 74 5 (by decide +kernel)
theorem q30_75:ThresholdAt 30 75:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 75 0 (by decide +kernel)
 · exact S 30 75 1 (by decide +kernel)
 · exact S 30 75 2 (by decide +kernel)
 · exact S 30 75 3 (by decide +kernel)
 · exact S 30 75 4 (by decide +kernel)
 · exact S 30 75 5 (by decide +kernel)
theorem q30_76:ThresholdAt 30 76:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 76 0 (by decide +kernel)
 · exact S 30 76 1 (by decide +kernel)
 · exact S 30 76 2 (by decide +kernel)
 · exact S 30 76 3 (by decide +kernel)
 · exact S 30 76 4 (by decide +kernel)
 · exact S 30 76 5 (by decide +kernel)
theorem q30_77:ThresholdAt 30 77:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 77 0 (by decide +kernel)
 · exact S 30 77 1 (by decide +kernel)
 · exact S 30 77 2 (by decide +kernel)
 · exact S 30 77 3 (by decide +kernel)
 · exact S 30 77 4 (by decide +kernel)
 · exact S 30 77 5 (by decide +kernel)
theorem q30_78:ThresholdAt 30 78:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 78 0 (by decide +kernel)
 · exact S 30 78 1 (by decide +kernel)
 · exact S 30 78 2 (by decide +kernel)
 · exact S 30 78 3 (by decide +kernel)
 · exact S 30 78 4 (by decide +kernel)
 · exact S 30 78 5 (by decide +kernel)
theorem q30_79:ThresholdAt 30 79:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 79 0 (by decide +kernel)
 · exact S 30 79 1 (by decide +kernel)
 · exact S 30 79 2 (by decide +kernel)
 · exact S 30 79 3 (by decide +kernel)
 · exact S 30 79 4 (by decide +kernel)
 · exact S 30 79 5 (by decide +kernel)
theorem q30_80:ThresholdAt 30 80:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 80 0 (by decide +kernel)
 · exact S 30 80 1 (by decide +kernel)
 · exact S 30 80 2 (by decide +kernel)
 · exact S 30 80 3 (by decide +kernel)
 · exact S 30 80 4 (by decide +kernel)
 · exact S 30 80 5 (by decide +kernel)
theorem q30_81:ThresholdAt 30 81:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 81 0 (by decide +kernel)
 · exact S 30 81 1 (by decide +kernel)
 · exact S 30 81 2 (by decide +kernel)
 · exact S 30 81 3 (by decide +kernel)
 · exact S 30 81 4 (by decide +kernel)
 · exact S 30 81 5 (by decide +kernel)
theorem q30_82:ThresholdAt 30 82:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 82 0 (by decide +kernel)
 · exact S 30 82 1 (by decide +kernel)
 · exact S 30 82 2 (by decide +kernel)
 · exact S 30 82 3 (by decide +kernel)
 · exact S 30 82 4 (by decide +kernel)
 · exact S 30 82 5 (by decide +kernel)
theorem q30_83:ThresholdAt 30 83:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 83 0 (by decide +kernel)
 · exact S 30 83 1 (by decide +kernel)
 · exact S 30 83 2 (by decide +kernel)
 · exact S 30 83 3 (by decide +kernel)
 · exact S 30 83 4 (by decide +kernel)
 · exact S 30 83 5 (by decide +kernel)
theorem q30_84:ThresholdAt 30 84:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 84 0 (by decide +kernel)
 · exact S 30 84 1 (by decide +kernel)
 · exact S 30 84 2 (by decide +kernel)
 · exact S 30 84 3 (by decide +kernel)
 · exact S 30 84 4 (by decide +kernel)
 · exact S 30 84 5 (by decide +kernel)
theorem q30_85:ThresholdAt 30 85:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 85 0 (by decide +kernel)
 · exact S 30 85 1 (by decide +kernel)
 · exact S 30 85 2 (by decide +kernel)
 · exact S 30 85 3 (by decide +kernel)
 · exact S 30 85 4 (by decide +kernel)
 · exact S 30 85 5 (by decide +kernel)
theorem q30_86:ThresholdAt 30 86:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 86 0 (by decide +kernel)
 · exact S 30 86 1 (by decide +kernel)
 · exact S 30 86 2 (by decide +kernel)
 · exact S 30 86 3 (by decide +kernel)
 · exact S 30 86 4 (by decide +kernel)
 · exact S 30 86 5 (by decide +kernel)
theorem q30_87:ThresholdAt 30 87:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 87 0 (by decide +kernel)
 · exact S 30 87 1 (by decide +kernel)
 · exact S 30 87 2 (by decide +kernel)
 · exact S 30 87 3 (by decide +kernel)
 · exact S 30 87 4 (by decide +kernel)
 · exact S 30 87 5 (by decide +kernel)
theorem q30_88:ThresholdAt 30 88:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 88 0 (by decide +kernel)
 · exact S 30 88 1 (by decide +kernel)
 · exact S 30 88 2 (by decide +kernel)
 · exact S 30 88 3 (by decide +kernel)
 · exact S 30 88 4 (by decide +kernel)
 · exact S 30 88 5 (by decide +kernel)
theorem q30_89:ThresholdAt 30 89:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 89 0 (by decide +kernel)
 · exact S 30 89 1 (by decide +kernel)
 · exact S 30 89 2 (by decide +kernel)
 · exact S 30 89 3 (by decide +kernel)
 · exact S 30 89 4 (by decide +kernel)
 · exact S 30 89 5 (by decide +kernel)
theorem q30_90:ThresholdAt 30 90:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 90 0 (by decide +kernel)
 · exact S 30 90 1 (by decide +kernel)
 · exact S 30 90 2 (by decide +kernel)
 · exact S 30 90 3 (by decide +kernel)
 · exact S 30 90 4 (by decide +kernel)
 · exact S 30 90 5 (by decide +kernel)
theorem q30_91:ThresholdAt 30 91:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 91 0 (by decide +kernel)
 · exact S 30 91 1 (by decide +kernel)
 · exact S 30 91 2 (by decide +kernel)
 · exact S 30 91 3 (by decide +kernel)
 · exact S 30 91 4 (by decide +kernel)
 · exact S 30 91 5 (by decide +kernel)
theorem q30_92:ThresholdAt 30 92:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 92 0 (by decide +kernel)
 · exact S 30 92 1 (by decide +kernel)
 · exact S 30 92 2 (by decide +kernel)
 · exact S 30 92 3 (by decide +kernel)
 · exact S 30 92 4 (by decide +kernel)
 · exact S 30 92 5 (by decide +kernel)
theorem q30_93:ThresholdAt 30 93:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 93 0 (by decide +kernel)
 · exact S 30 93 1 (by decide +kernel)
 · exact S 30 93 2 (by decide +kernel)
 · exact S 30 93 3 (by decide +kernel)
 · exact S 30 93 4 (by decide +kernel)
 · exact S 30 93 5 (by decide +kernel)
theorem q30_94:ThresholdAt 30 94:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 94 0 (by decide +kernel)
 · exact S 30 94 1 (by decide +kernel)
 · exact S 30 94 2 (by decide +kernel)
 · exact S 30 94 3 (by decide +kernel)
 · exact S 30 94 4 (by decide +kernel)
 · exact S 30 94 5 (by decide +kernel)
theorem q30_95:ThresholdAt 30 95:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 95 0 (by decide +kernel)
 · exact S 30 95 1 (by decide +kernel)
 · exact S 30 95 2 (by decide +kernel)
 · exact S 30 95 3 (by decide +kernel)
 · exact S 30 95 4 (by decide +kernel)
 · exact S 30 95 5 (by decide +kernel)
theorem q30_96:ThresholdAt 30 96:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 96 0 (by decide +kernel)
 · exact S 30 96 1 (by decide +kernel)
 · exact S 30 96 2 (by decide +kernel)
 · exact S 30 96 3 (by decide +kernel)
 · exact S 30 96 4 (by decide +kernel)
 · exact S 30 96 5 (by decide +kernel)
theorem q30_97:ThresholdAt 30 97:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 97 0 (by decide +kernel)
 · exact S 30 97 1 (by decide +kernel)
 · exact S 30 97 2 (by decide +kernel)
 · exact S 30 97 3 (by decide +kernel)
 · exact S 30 97 4 (by decide +kernel)
 · exact S 30 97 5 (by decide +kernel)
theorem q30_98:ThresholdAt 30 98:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 98 0 (by decide +kernel)
 · exact S 30 98 1 (by decide +kernel)
 · exact S 30 98 2 (by decide +kernel)
 · exact S 30 98 3 (by decide +kernel)
 · exact S 30 98 4 (by decide +kernel)
 · exact S 30 98 5 (by decide +kernel)
theorem q30_99:ThresholdAt 30 99:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 99 0 (by decide +kernel)
 · exact S 30 99 1 (by decide +kernel)
 · exact S 30 99 2 (by decide +kernel)
 · exact S 30 99 3 (by decide +kernel)
 · exact S 30 99 4 (by decide +kernel)
 · exact S 30 99 5 (by decide +kernel)
theorem q30_100:ThresholdAt 30 100:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 100 0 (by decide +kernel)
 · exact S 30 100 1 (by decide +kernel)
 · exact S 30 100 2 (by decide +kernel)
 · exact S 30 100 3 (by decide +kernel)
 · exact S 30 100 4 (by decide +kernel)
 · exact S 30 100 5 (by decide +kernel)
theorem q30_101:ThresholdAt 30 101:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 101 0 (by decide +kernel)
 · exact S 30 101 1 (by decide +kernel)
 · exact S 30 101 2 (by decide +kernel)
 · exact S 30 101 3 (by decide +kernel)
 · exact S 30 101 4 (by decide +kernel)
 · exact S 30 101 5 (by decide +kernel)
theorem q30_102:ThresholdAt 30 102:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 102 0 (by decide +kernel)
 · exact S 30 102 1 (by decide +kernel)
 · exact S 30 102 2 (by decide +kernel)
 · exact S 30 102 3 (by decide +kernel)
 · exact S 30 102 4 (by decide +kernel)
 · exact S 30 102 5 (by decide +kernel)
theorem q30_103:ThresholdAt 30 103:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 103 0 (by decide +kernel)
 · exact S 30 103 1 (by decide +kernel)
 · exact S 30 103 2 (by decide +kernel)
 · exact S 30 103 3 (by decide +kernel)
 · exact S 30 103 4 (by decide +kernel)
 · exact S 30 103 5 (by decide +kernel)
theorem q30_104:ThresholdAt 30 104:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 104 0 (by decide +kernel)
 · exact S 30 104 1 (by decide +kernel)
 · exact S 30 104 2 (by decide +kernel)
 · exact S 30 104 3 (by decide +kernel)
 · exact S 30 104 4 (by decide +kernel)
 · exact S 30 104 5 (by decide +kernel)
theorem q30_105:ThresholdAt 30 105:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 105 0 (by decide +kernel)
 · exact S 30 105 1 (by decide +kernel)
 · exact S 30 105 2 (by decide +kernel)
 · exact S 30 105 3 (by decide +kernel)
 · exact S 30 105 4 (by decide +kernel)
 · exact S 30 105 5 (by decide +kernel)
theorem q30_106:ThresholdAt 30 106:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 106 0 (by decide +kernel)
 · exact S 30 106 1 (by decide +kernel)
 · exact S 30 106 2 (by decide +kernel)
 · exact S 30 106 3 (by decide +kernel)
 · exact S 30 106 4 (by decide +kernel)
 · exact S 30 106 5 (by decide +kernel)
theorem q30_107:ThresholdAt 30 107:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 107 0 (by decide +kernel)
 · exact S 30 107 1 (by decide +kernel)
 · exact S 30 107 2 (by decide +kernel)
 · exact S 30 107 3 (by decide +kernel)
 · exact S 30 107 4 (by decide +kernel)
 · exact S 30 107 5 (by decide +kernel)
theorem q30_108:ThresholdAt 30 108:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 108 0 (by decide +kernel)
 · exact S 30 108 1 (by decide +kernel)
 · exact S 30 108 2 (by decide +kernel)
 · exact S 30 108 3 (by decide +kernel)
 · exact S 30 108 4 (by decide +kernel)
 · exact S 30 108 5 (by decide +kernel)
theorem q30_109:ThresholdAt 30 109:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 109 0 (by decide +kernel)
 · exact S 30 109 1 (by decide +kernel)
 · exact S 30 109 2 (by decide +kernel)
 · exact S 30 109 3 (by decide +kernel)
 · exact S 30 109 4 (by decide +kernel)
 · exact S 30 109 5 (by decide +kernel)
theorem q30_110:ThresholdAt 30 110:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 110 0 (by decide +kernel)
 · exact S 30 110 1 (by decide +kernel)
 · exact S 30 110 2 (by decide +kernel)
 · exact S 30 110 3 (by decide +kernel)
 · exact S 30 110 4 (by decide +kernel)
 · exact S 30 110 5 (by decide +kernel)
theorem q30_111:ThresholdAt 30 111:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 111 0 (by decide +kernel)
 · exact S 30 111 1 (by decide +kernel)
 · exact S 30 111 2 (by decide +kernel)
 · exact S 30 111 3 (by decide +kernel)
 · exact S 30 111 4 (by decide +kernel)
 · exact S 30 111 5 (by decide +kernel)
theorem q30_112:ThresholdAt 30 112:=by
 intro j hj
 have hj6:j < 6:=List.mem_range.mp hj
 interval_cases j
 · exact S 30 112 0 (by decide +kernel)
 · exact S 30 112 1 (by decide +kernel)
 · exact S 30 112 2 (by decide +kernel)
 · exact S 30 112 3 (by decide +kernel)
 · exact S 30 112 4 (by decide +kernel)
 · exact S 30 112 5 (by decide +kernel)
theorem checkedR30:∀ V ∈ List.range 113,ThresholdAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0_113:V < 56
  · by_cases h0_56:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have he:V = 0:=by omega
              subst V
              exact q30_0
            · by_cases h1_3:V < 2
              · have he:V = 1:=by omega
                subst V
                exact q30_1
              · have he:V = 2:=by omega
                subst V
                exact q30_2
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have he:V = 3:=by omega
                subst V
                exact q30_3
              · have he:V = 4:=by omega
                subst V
                exact q30_4
            · by_cases h5_7:V < 6
              · have he:V = 5:=by omega
                subst V
                exact q30_5
              · have he:V = 6:=by omega
                subst V
                exact q30_6
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have he:V = 7:=by omega
              subst V
              exact q30_7
            · by_cases h8_10:V < 9
              · have he:V = 8:=by omega
                subst V
                exact q30_8
              · have he:V = 9:=by omega
                subst V
                exact q30_9
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have he:V = 10:=by omega
                subst V
                exact q30_10
              · have he:V = 11:=by omega
                subst V
                exact q30_11
            · by_cases h12_14:V < 13
              · have he:V = 12:=by omega
                subst V
                exact q30_12
              · have he:V = 13:=by omega
                subst V
                exact q30_13
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have he:V = 14:=by omega
              subst V
              exact q30_14
            · by_cases h15_17:V < 16
              · have he:V = 15:=by omega
                subst V
                exact q30_15
              · have he:V = 16:=by omega
                subst V
                exact q30_16
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have he:V = 17:=by omega
                subst V
                exact q30_17
              · have he:V = 18:=by omega
                subst V
                exact q30_18
            · by_cases h19_21:V < 20
              · have he:V = 19:=by omega
                subst V
                exact q30_19
              · have he:V = 20:=by omega
                subst V
                exact q30_20
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have he:V = 21:=by omega
              subst V
              exact q30_21
            · by_cases h22_24:V < 23
              · have he:V = 22:=by omega
                subst V
                exact q30_22
              · have he:V = 23:=by omega
                subst V
                exact q30_23
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have he:V = 24:=by omega
                subst V
                exact q30_24
              · have he:V = 25:=by omega
                subst V
                exact q30_25
            · by_cases h26_28:V < 27
              · have he:V = 26:=by omega
                subst V
                exact q30_26
              · have he:V = 27:=by omega
                subst V
                exact q30_27
    · by_cases h28_56:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have he:V = 28:=by omega
              subst V
              exact q30_28
            · by_cases h29_31:V < 30
              · have he:V = 29:=by omega
                subst V
                exact q30_29
              · have he:V = 30:=by omega
                subst V
                exact q30_30
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have he:V = 31:=by omega
                subst V
                exact q30_31
              · have he:V = 32:=by omega
                subst V
                exact q30_32
            · by_cases h33_35:V < 34
              · have he:V = 33:=by omega
                subst V
                exact q30_33
              · have he:V = 34:=by omega
                subst V
                exact q30_34
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have he:V = 35:=by omega
              subst V
              exact q30_35
            · by_cases h36_38:V < 37
              · have he:V = 36:=by omega
                subst V
                exact q30_36
              · have he:V = 37:=by omega
                subst V
                exact q30_37
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have he:V = 38:=by omega
                subst V
                exact q30_38
              · have he:V = 39:=by omega
                subst V
                exact q30_39
            · by_cases h40_42:V < 41
              · have he:V = 40:=by omega
                subst V
                exact q30_40
              · have he:V = 41:=by omega
                subst V
                exact q30_41
      · by_cases h42_56:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have he:V = 42:=by omega
              subst V
              exact q30_42
            · by_cases h43_45:V < 44
              · have he:V = 43:=by omega
                subst V
                exact q30_43
              · have he:V = 44:=by omega
                subst V
                exact q30_44
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have he:V = 45:=by omega
                subst V
                exact q30_45
              · have he:V = 46:=by omega
                subst V
                exact q30_46
            · by_cases h47_49:V < 48
              · have he:V = 47:=by omega
                subst V
                exact q30_47
              · have he:V = 48:=by omega
                subst V
                exact q30_48
        · by_cases h49_56:V < 52
          · by_cases h49_52:V < 50
            · have he:V = 49:=by omega
              subst V
              exact q30_49
            · by_cases h50_52:V < 51
              · have he:V = 50:=by omega
                subst V
                exact q30_50
              · have he:V = 51:=by omega
                subst V
                exact q30_51
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have he:V = 52:=by omega
                subst V
                exact q30_52
              · have he:V = 53:=by omega
                subst V
                exact q30_53
            · by_cases h54_56:V < 55
              · have he:V = 54:=by omega
                subst V
                exact q30_54
              · have he:V = 55:=by omega
                subst V
                exact q30_55
  · by_cases h56_113:V < 84
    · by_cases h56_84:V < 70
      · by_cases h56_70:V < 63
        · by_cases h56_63:V < 59
          · by_cases h56_59:V < 57
            · have he:V = 56:=by omega
              subst V
              exact q30_56
            · by_cases h57_59:V < 58
              · have he:V = 57:=by omega
                subst V
                exact q30_57
              · have he:V = 58:=by omega
                subst V
                exact q30_58
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have he:V = 59:=by omega
                subst V
                exact q30_59
              · have he:V = 60:=by omega
                subst V
                exact q30_60
            · by_cases h61_63:V < 62
              · have he:V = 61:=by omega
                subst V
                exact q30_61
              · have he:V = 62:=by omega
                subst V
                exact q30_62
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have he:V = 63:=by omega
              subst V
              exact q30_63
            · by_cases h64_66:V < 65
              · have he:V = 64:=by omega
                subst V
                exact q30_64
              · have he:V = 65:=by omega
                subst V
                exact q30_65
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have he:V = 66:=by omega
                subst V
                exact q30_66
              · have he:V = 67:=by omega
                subst V
                exact q30_67
            · by_cases h68_70:V < 69
              · have he:V = 68:=by omega
                subst V
                exact q30_68
              · have he:V = 69:=by omega
                subst V
                exact q30_69
      · by_cases h70_84:V < 77
        · by_cases h70_77:V < 73
          · by_cases h70_73:V < 71
            · have he:V = 70:=by omega
              subst V
              exact q30_70
            · by_cases h71_73:V < 72
              · have he:V = 71:=by omega
                subst V
                exact q30_71
              · have he:V = 72:=by omega
                subst V
                exact q30_72
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have he:V = 73:=by omega
                subst V
                exact q30_73
              · have he:V = 74:=by omega
                subst V
                exact q30_74
            · by_cases h75_77:V < 76
              · have he:V = 75:=by omega
                subst V
                exact q30_75
              · have he:V = 76:=by omega
                subst V
                exact q30_76
        · by_cases h77_84:V < 80
          · by_cases h77_80:V < 78
            · have he:V = 77:=by omega
              subst V
              exact q30_77
            · by_cases h78_80:V < 79
              · have he:V = 78:=by omega
                subst V
                exact q30_78
              · have he:V = 79:=by omega
                subst V
                exact q30_79
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have he:V = 80:=by omega
                subst V
                exact q30_80
              · have he:V = 81:=by omega
                subst V
                exact q30_81
            · by_cases h82_84:V < 83
              · have he:V = 82:=by omega
                subst V
                exact q30_82
              · have he:V = 83:=by omega
                subst V
                exact q30_83
    · by_cases h84_113:V < 98
      · by_cases h84_98:V < 91
        · by_cases h84_91:V < 87
          · by_cases h84_87:V < 85
            · have he:V = 84:=by omega
              subst V
              exact q30_84
            · by_cases h85_87:V < 86
              · have he:V = 85:=by omega
                subst V
                exact q30_85
              · have he:V = 86:=by omega
                subst V
                exact q30_86
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have he:V = 87:=by omega
                subst V
                exact q30_87
              · have he:V = 88:=by omega
                subst V
                exact q30_88
            · by_cases h89_91:V < 90
              · have he:V = 89:=by omega
                subst V
                exact q30_89
              · have he:V = 90:=by omega
                subst V
                exact q30_90
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have he:V = 91:=by omega
              subst V
              exact q30_91
            · by_cases h92_94:V < 93
              · have he:V = 92:=by omega
                subst V
                exact q30_92
              · have he:V = 93:=by omega
                subst V
                exact q30_93
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have he:V = 94:=by omega
                subst V
                exact q30_94
              · have he:V = 95:=by omega
                subst V
                exact q30_95
            · by_cases h96_98:V < 97
              · have he:V = 96:=by omega
                subst V
                exact q30_96
              · have he:V = 97:=by omega
                subst V
                exact q30_97
      · by_cases h98_113:V < 105
        · by_cases h98_105:V < 101
          · by_cases h98_101:V < 99
            · have he:V = 98:=by omega
              subst V
              exact q30_98
            · by_cases h99_101:V < 100
              · have he:V = 99:=by omega
                subst V
                exact q30_99
              · have he:V = 100:=by omega
                subst V
                exact q30_100
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have he:V = 101:=by omega
                subst V
                exact q30_101
              · have he:V = 102:=by omega
                subst V
                exact q30_102
            · by_cases h103_105:V < 104
              · have he:V = 103:=by omega
                subst V
                exact q30_103
              · have he:V = 104:=by omega
                subst V
                exact q30_104
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have he:V = 105:=by omega
                subst V
                exact q30_105
              · have he:V = 106:=by omega
                subst V
                exact q30_106
            · by_cases h107_109:V < 108
              · have he:V = 107:=by omega
                subst V
                exact q30_107
              · have he:V = 108:=by omega
                subst V
                exact q30_108
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have he:V = 109:=by omega
                subst V
                exact q30_109
              · have he:V = 110:=by omega
                subst V
                exact q30_110
            · by_cases h111_113:V < 112
              · have he:V = 111:=by omega
                subst V
                exact q30_111
              · have he:V = 112:=by omega
                subst V
                exact q30_112
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
