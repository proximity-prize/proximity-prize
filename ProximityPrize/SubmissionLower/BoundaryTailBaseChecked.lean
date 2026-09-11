import ProximityPrize.SubmissionLower.BoundaryTailBaseBlock04
import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem correctAll : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → CorrectAt R V := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact correct_r1 V (List.mem_range.mpr (by omega))
    | exact correct_r2 V (List.mem_range.mpr (by omega))
    | exact correct_r3 V (List.mem_range.mpr (by omega))
    | exact correct_r4 V (List.mem_range.mpr (by omega))
    | exact correct_r5 V (List.mem_range.mpr (by omega))
    | exact correct_r6 V (List.mem_range.mpr (by omega))
    | exact correct_r7 V (List.mem_range.mpr (by omega))
    | exact correct_r8 V (List.mem_range.mpr (by omega))
    | exact correct_r9 V (List.mem_range.mpr (by omega))
    | exact correct_r10 V (List.mem_range.mpr (by omega))
    | exact correct_r11 V (List.mem_range.mpr (by omega))
    | exact correct_r12 V (List.mem_range.mpr (by omega))
    | exact correct_r13 V (List.mem_range.mpr (by omega))
    | exact correct_r14 V (List.mem_range.mpr (by omega))
    | exact correct_r15 V (List.mem_range.mpr (by omega))
    | exact correct_r16 V (List.mem_range.mpr (by omega))
    | exact correct_r17 V (List.mem_range.mpr (by omega))
    | exact correct_r18 V (List.mem_range.mpr (by omega))
    | exact correct_r19 V (List.mem_range.mpr (by omega))
    | exact correct_r20 V (List.mem_range.mpr (by omega))
    | exact correct_r21 V (List.mem_range.mpr (by omega))
    | exact correct_r22 V (List.mem_range.mpr (by omega))
    | exact correct_r23 V (List.mem_range.mpr (by omega))
    | exact correct_r24 V (List.mem_range.mpr (by omega))
    | exact correct_r25 V (List.mem_range.mpr (by omega))
    | exact correct_r26 V (List.mem_range.mpr (by omega))
    | exact correct_r27 V (List.mem_range.mpr (by omega))
    | exact correct_r28 V (List.mem_range.mpr (by omega))
    | exact correct_r29 V (List.mem_range.mpr (by omega))
    | exact correct_r30 V (List.mem_range.mpr (by omega))
    | exact correct_r31 V (List.mem_range.mpr (by omega))
theorem zeroAll : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → ZeroCheckAt R V := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact zero_r1 V (List.mem_range.mpr (by omega))
    | exact zero_r2 V (List.mem_range.mpr (by omega))
    | exact zero_r3 V (List.mem_range.mpr (by omega))
    | exact zero_r4 V (List.mem_range.mpr (by omega))
    | exact zero_r5 V (List.mem_range.mpr (by omega))
    | exact zero_r6 V (List.mem_range.mpr (by omega))
    | exact zero_r7 V (List.mem_range.mpr (by omega))
    | exact zero_r8 V (List.mem_range.mpr (by omega))
    | exact zero_r9 V (List.mem_range.mpr (by omega))
    | exact zero_r10 V (List.mem_range.mpr (by omega))
    | exact zero_r11 V (List.mem_range.mpr (by omega))
    | exact zero_r12 V (List.mem_range.mpr (by omega))
    | exact zero_r13 V (List.mem_range.mpr (by omega))
    | exact zero_r14 V (List.mem_range.mpr (by omega))
    | exact zero_r15 V (List.mem_range.mpr (by omega))
    | exact zero_r16 V (List.mem_range.mpr (by omega))
    | exact zero_r17 V (List.mem_range.mpr (by omega))
    | exact zero_r18 V (List.mem_range.mpr (by omega))
    | exact zero_r19 V (List.mem_range.mpr (by omega))
    | exact zero_r20 V (List.mem_range.mpr (by omega))
    | exact zero_r21 V (List.mem_range.mpr (by omega))
    | exact zero_r22 V (List.mem_range.mpr (by omega))
    | exact zero_r23 V (List.mem_range.mpr (by omega))
    | exact zero_r24 V (List.mem_range.mpr (by omega))
    | exact zero_r25 V (List.mem_range.mpr (by omega))
    | exact zero_r26 V (List.mem_range.mpr (by omega))
    | exact zero_r27 V (List.mem_range.mpr (by omega))
    | exact zero_r28 V (List.mem_range.mpr (by omega))
    | exact zero_r29 V (List.mem_range.mpr (by omega))
    | exact zero_r30 V (List.mem_range.mpr (by omega))
    | exact zero_r31 V (List.mem_range.mpr (by omega))
theorem strictAll : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → StrictCheckAt R V := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact strict_r1 V (List.mem_range.mpr (by omega))
    | exact strict_r2 V (List.mem_range.mpr (by omega))
    | exact strict_r3 V (List.mem_range.mpr (by omega))
    | exact strict_r4 V (List.mem_range.mpr (by omega))
    | exact strict_r5 V (List.mem_range.mpr (by omega))
    | exact strict_r6 V (List.mem_range.mpr (by omega))
    | exact strict_r7 V (List.mem_range.mpr (by omega))
    | exact strict_r8 V (List.mem_range.mpr (by omega))
    | exact strict_r9 V (List.mem_range.mpr (by omega))
    | exact strict_r10 V (List.mem_range.mpr (by omega))
    | exact strict_r11 V (List.mem_range.mpr (by omega))
    | exact strict_r12 V (List.mem_range.mpr (by omega))
    | exact strict_r13 V (List.mem_range.mpr (by omega))
    | exact strict_r14 V (List.mem_range.mpr (by omega))
    | exact strict_r15 V (List.mem_range.mpr (by omega))
    | exact strict_r16 V (List.mem_range.mpr (by omega))
    | exact strict_r17 V (List.mem_range.mpr (by omega))
    | exact strict_r18 V (List.mem_range.mpr (by omega))
    | exact strict_r19 V (List.mem_range.mpr (by omega))
    | exact strict_r20 V (List.mem_range.mpr (by omega))
    | exact strict_r21 V (List.mem_range.mpr (by omega))
    | exact strict_r22 V (List.mem_range.mpr (by omega))
    | exact strict_r23 V (List.mem_range.mpr (by omega))
    | exact strict_r24 V (List.mem_range.mpr (by omega))
    | exact strict_r25 V (List.mem_range.mpr (by omega))
    | exact strict_r26 V (List.mem_range.mpr (by omega))
    | exact strict_r27 V (List.mem_range.mpr (by omega))
    | exact strict_r28 V (List.mem_range.mpr (by omega))
    | exact strict_r29 V (List.mem_range.mpr (by omega))
    | exact strict_r30 V (List.mem_range.mpr (by omega))
    | exact strict_r31 V (List.mem_range.mpr (by omega))
theorem baseAll : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → BaseCheckAt R V := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact base_r1 V (List.mem_range.mpr (by omega))
    | exact base_r2 V (List.mem_range.mpr (by omega))
    | exact base_r3 V (List.mem_range.mpr (by omega))
    | exact base_r4 V (List.mem_range.mpr (by omega))
    | exact base_r5 V (List.mem_range.mpr (by omega))
    | exact base_r6 V (List.mem_range.mpr (by omega))
    | exact base_r7 V (List.mem_range.mpr (by omega))
    | exact base_r8 V (List.mem_range.mpr (by omega))
    | exact base_r9 V (List.mem_range.mpr (by omega))
    | exact base_r10 V (List.mem_range.mpr (by omega))
    | exact base_r11 V (List.mem_range.mpr (by omega))
    | exact base_r12 V (List.mem_range.mpr (by omega))
    | exact base_r13 V (List.mem_range.mpr (by omega))
    | exact base_r14 V (List.mem_range.mpr (by omega))
    | exact base_r15 V (List.mem_range.mpr (by omega))
    | exact base_r16 V (List.mem_range.mpr (by omega))
    | exact base_r17 V (List.mem_range.mpr (by omega))
    | exact base_r18 V (List.mem_range.mpr (by omega))
    | exact base_r19 V (List.mem_range.mpr (by omega))
    | exact base_r20 V (List.mem_range.mpr (by omega))
    | exact base_r21 V (List.mem_range.mpr (by omega))
    | exact base_r22 V (List.mem_range.mpr (by omega))
    | exact base_r23 V (List.mem_range.mpr (by omega))
    | exact base_r24 V (List.mem_range.mpr (by omega))
    | exact base_r25 V (List.mem_range.mpr (by omega))
    | exact base_r26 V (List.mem_range.mpr (by omega))
    | exact base_r27 V (List.mem_range.mpr (by omega))
    | exact base_r28 V (List.mem_range.mpr (by omega))
    | exact base_r29 V (List.mem_range.mpr (by omega))
    | exact base_r30 V (List.mem_range.mpr (by omega))
    | exact base_r31 V (List.mem_range.mpr (by omega))
theorem receipt : BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap BoundaryTailBaseData.cap :=
  receipt_of_checks carriers runs correctAll zeroAll strictAll baseAll

theorem phaseReceipt : BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap (Lower80811.PhaseSemantics.phaseCap 0) := by
  convert receipt using 1
  funext p
  rfl
end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
