import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked06

namespace ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
open Lower80801.PhaseSemantics
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem prefixReceipt : PrefixReceiptSound := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact prefix_r1 V (List.mem_range.mpr (by omega))
    | exact prefix_r2 V (List.mem_range.mpr (by omega))
    | exact prefix_r3 V (List.mem_range.mpr (by omega))
    | exact prefix_r4 V (List.mem_range.mpr (by omega))
    | exact prefix_r5 V (List.mem_range.mpr (by omega))
    | exact prefix_r6 V (List.mem_range.mpr (by omega))
    | exact prefix_r7 V (List.mem_range.mpr (by omega))
    | exact prefix_r8 V (List.mem_range.mpr (by omega))
    | exact prefix_r9 V (List.mem_range.mpr (by omega))
    | exact prefix_r10 V (List.mem_range.mpr (by omega))
    | exact prefix_r11 V (List.mem_range.mpr (by omega))
    | exact prefix_r12 V (List.mem_range.mpr (by omega))
    | exact prefix_r13 V (List.mem_range.mpr (by omega))
    | exact prefix_r14 V (List.mem_range.mpr (by omega))
    | exact prefix_r15 V (List.mem_range.mpr (by omega))
    | exact prefix_r16 V (List.mem_range.mpr (by omega))
    | exact prefix_r17 V (List.mem_range.mpr (by omega))
    | exact prefix_r18 V (List.mem_range.mpr (by omega))
    | exact prefix_r19 V (List.mem_range.mpr (by omega))
    | exact prefix_r20 V (List.mem_range.mpr (by omega))
    | exact prefix_r21 V (List.mem_range.mpr (by omega))
    | exact prefix_r22 V (List.mem_range.mpr (by omega))
    | exact prefix_r23 V (List.mem_range.mpr (by omega))
    | exact prefix_r24 V (List.mem_range.mpr (by omega))
    | exact prefix_r25 V (List.mem_range.mpr (by omega))
    | exact prefix_r26 V (List.mem_range.mpr (by omega))
    | exact prefix_r27 V (List.mem_range.mpr (by omega))
    | exact prefix_r28 V (List.mem_range.mpr (by omega))
    | exact prefix_r29 V (List.mem_range.mpr (by omega))
    | exact prefix_r30 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80801.PhaseChecked
