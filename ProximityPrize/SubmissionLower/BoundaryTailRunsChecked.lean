import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked07

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseSemantics
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem runsReceipt:RunReceiptSound:=by
  intro R V hR hRmax hRV
  interval_cases R
  · exact runs_r1 V (List.mem_range.mpr (by omega))
  · exact runs_r2 V (List.mem_range.mpr (by omega))
  · exact runs_r3 V (List.mem_range.mpr (by omega))
  · exact runs_r4 V (List.mem_range.mpr (by omega))
  · exact runs_r5 V (List.mem_range.mpr (by omega))
  · exact runs_r6 V (List.mem_range.mpr (by omega))
  · exact runs_r7 V (List.mem_range.mpr (by omega))
  · exact runs_r8 V (List.mem_range.mpr (by omega))
  · exact runs_r9 V (List.mem_range.mpr (by omega))
  · exact runs_r10 V (List.mem_range.mpr (by omega))
  · exact runs_r11 V (List.mem_range.mpr (by omega))
  · exact runs_r12 V (List.mem_range.mpr (by omega))
  · exact runs_r13 V (List.mem_range.mpr (by omega))
  · exact runs_r14 V (List.mem_range.mpr (by omega))
  · exact runs_r15 V (List.mem_range.mpr (by omega))
  · exact runs_r16 V (List.mem_range.mpr (by omega))
  · exact runs_r17 V (List.mem_range.mpr (by omega))
  · exact runs_r18 V (List.mem_range.mpr (by omega))
  · exact runs_r19 V (List.mem_range.mpr (by omega))
  · exact runs_r20 V (List.mem_range.mpr (by omega))
  · exact runs_r21 V (List.mem_range.mpr (by omega))
  · exact runs_r22 V (List.mem_range.mpr (by omega))
  · exact runs_r23 V (List.mem_range.mpr (by omega))
  · exact runs_r24 V (List.mem_range.mpr (by omega))
  · exact runs_r25 V (List.mem_range.mpr (by omega))
  · exact runs_r26 V (List.mem_range.mpr (by omega))
  · exact runs_r27 V (List.mem_range.mpr (by omega))
  · exact runs_r28 V (List.mem_range.mpr (by omega))
  · exact runs_r29 V (List.mem_range.mpr (by omega))
  · exact runs_r30 V (List.mem_range.mpr (by omega))
  · exact runs_r31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
