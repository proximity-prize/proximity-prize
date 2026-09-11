import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData

/-! `carriers` agrees with the closed form on every admissible cell. -/

namespace ProximityPrize.SubmissionLower.BoundaryTailCarrierChecked
open ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData
open ProximityPrize.SubmissionLower.BoundaryTailCarrierClosed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem car_eq_r1 : ∀ V ∈ List.range 139, carriers 1 V = carClosed 1 V := by
  decide +kernel

theorem car_eq_r2 : ∀ V ∈ List.range 138, carriers 2 V = carClosed 2 V := by
  decide +kernel

theorem car_eq_r3 : ∀ V ∈ List.range 137, carriers 3 V = carClosed 3 V := by
  decide +kernel

theorem car_eq_r4 : ∀ V ∈ List.range 136, carriers 4 V = carClosed 4 V := by
  decide +kernel

theorem car_eq_r5 : ∀ V ∈ List.range 135, carriers 5 V = carClosed 5 V := by
  decide +kernel

theorem car_eq_r6 : ∀ V ∈ List.range 134, carriers 6 V = carClosed 6 V := by
  decide +kernel

theorem car_eq_r7 : ∀ V ∈ List.range 133, carriers 7 V = carClosed 7 V := by
  decide +kernel

theorem car_eq_r8 : ∀ V ∈ List.range 132, carriers 8 V = carClosed 8 V := by
  decide +kernel

theorem car_eq_r9 : ∀ V ∈ List.range 131, carriers 9 V = carClosed 9 V := by
  decide +kernel

theorem car_eq_r10 : ∀ V ∈ List.range 130, carriers 10 V = carClosed 10 V := by
  decide +kernel

theorem car_eq_r11 : ∀ V ∈ List.range 129, carriers 11 V = carClosed 11 V := by
  decide +kernel

theorem car_eq_r12 : ∀ V ∈ List.range 128, carriers 12 V = carClosed 12 V := by
  decide +kernel

theorem car_eq_r13 : ∀ V ∈ List.range 127, carriers 13 V = carClosed 13 V := by
  decide +kernel

theorem car_eq_r14 : ∀ V ∈ List.range 126, carriers 14 V = carClosed 14 V := by
  decide +kernel

theorem car_eq_r15 : ∀ V ∈ List.range 125, carriers 15 V = carClosed 15 V := by
  decide +kernel

theorem car_eq_r16 : ∀ V ∈ List.range 124, carriers 16 V = carClosed 16 V := by
  decide +kernel

theorem car_eq_r17 : ∀ V ∈ List.range 123, carriers 17 V = carClosed 17 V := by
  decide +kernel

theorem car_eq_r18 : ∀ V ∈ List.range 122, carriers 18 V = carClosed 18 V := by
  decide +kernel

theorem car_eq_r19 : ∀ V ∈ List.range 121, carriers 19 V = carClosed 19 V := by
  decide +kernel

theorem car_eq_r20 : ∀ V ∈ List.range 120, carriers 20 V = carClosed 20 V := by
  decide +kernel

theorem car_eq_r21 : ∀ V ∈ List.range 119, carriers 21 V = carClosed 21 V := by
  decide +kernel

theorem car_eq_r22 : ∀ V ∈ List.range 118, carriers 22 V = carClosed 22 V := by
  decide +kernel

theorem car_eq_r23 : ∀ V ∈ List.range 117, carriers 23 V = carClosed 23 V := by
  decide +kernel

theorem car_eq_r24 : ∀ V ∈ List.range 116, carriers 24 V = carClosed 24 V := by
  decide +kernel

theorem car_eq_r25 : ∀ V ∈ List.range 115, carriers 25 V = carClosed 25 V := by
  decide +kernel

theorem car_eq_r26 : ∀ V ∈ List.range 114, carriers 26 V = carClosed 26 V := by
  decide +kernel

theorem car_eq_r27 : ∀ V ∈ List.range 113, carriers 27 V = carClosed 27 V := by
  decide +kernel

theorem car_eq_r28 : ∀ V ∈ List.range 112, carriers 28 V = carClosed 28 V := by
  decide +kernel

theorem car_eq_r29 : ∀ V ∈ List.range 111, carriers 29 V = carClosed 29 V := by
  decide +kernel

theorem car_eq_r30 : ∀ V ∈ List.range 110, carriers 30 V = carClosed 30 V := by
  decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailCarrierChecked
