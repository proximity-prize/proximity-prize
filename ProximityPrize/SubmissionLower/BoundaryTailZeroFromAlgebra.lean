import ProximityPrize.SubmissionLower.BoundaryTailZeroClosed
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData

/- PR541 algebra adapted to the audited 68.06 rows 1..31. -/
set_option Elab.async false

/-!
`ZeroAt` without enumerating the splits.

The shipped receipts check, for every `(R,V)` and every split `(r,v)`, that
`c0 r v + zero (R-r) (V-v) ≤ zero R V` — about 3.1M kernel points.  The same
statement follows from two facts:

* `c0 r v ≤ zero r v`                     (one bounded check per row), and
* superadditivity of `zero`               (`zero_superadd`, mostly algebra).
-/

namespace ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open ProximityPrize.SubmissionLower.BoundaryTailStrictData
open ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData
open ProximityPrize.SubmissionLower.BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroClosed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem c0_le_zero_r1 : ∀ v ∈ List.range 142, (carriers 1 v).c0 ≤ zero 1 v := by
  decide +kernel

theorem c0_le_zero_r2 : ∀ v ∈ List.range 141, (carriers 2 v).c0 ≤ zero 2 v := by
  decide +kernel

theorem c0_le_zero_r3 : ∀ v ∈ List.range 140, (carriers 3 v).c0 ≤ zero 3 v := by
  decide +kernel

theorem c0_le_zero_r4 : ∀ v ∈ List.range 139, (carriers 4 v).c0 ≤ zero 4 v := by
  decide +kernel

theorem c0_le_zero_r5 : ∀ v ∈ List.range 138, (carriers 5 v).c0 ≤ zero 5 v := by
  decide +kernel

theorem c0_le_zero_r6 : ∀ v ∈ List.range 137, (carriers 6 v).c0 ≤ zero 6 v := by
  decide +kernel

theorem c0_le_zero_r7 : ∀ v ∈ List.range 136, (carriers 7 v).c0 ≤ zero 7 v := by
  decide +kernel

theorem c0_le_zero_r8 : ∀ v ∈ List.range 135, (carriers 8 v).c0 ≤ zero 8 v := by
  decide +kernel

theorem c0_le_zero_r9 : ∀ v ∈ List.range 134, (carriers 9 v).c0 ≤ zero 9 v := by
  decide +kernel

theorem c0_le_zero_r10 : ∀ v ∈ List.range 133, (carriers 10 v).c0 ≤ zero 10 v := by
  decide +kernel

theorem c0_le_zero_r11 : ∀ v ∈ List.range 132, (carriers 11 v).c0 ≤ zero 11 v := by
  decide +kernel

theorem c0_le_zero_r12 : ∀ v ∈ List.range 131, (carriers 12 v).c0 ≤ zero 12 v := by
  decide +kernel

theorem c0_le_zero_r13 : ∀ v ∈ List.range 130, (carriers 13 v).c0 ≤ zero 13 v := by
  decide +kernel

theorem c0_le_zero_r14 : ∀ v ∈ List.range 129, (carriers 14 v).c0 ≤ zero 14 v := by
  decide +kernel

theorem c0_le_zero_r15 : ∀ v ∈ List.range 128, (carriers 15 v).c0 ≤ zero 15 v := by
  decide +kernel

theorem c0_le_zero_r16 : ∀ v ∈ List.range 127, (carriers 16 v).c0 ≤ zero 16 v := by
  decide +kernel

theorem c0_le_zero_r17 : ∀ v ∈ List.range 126, (carriers 17 v).c0 ≤ zero 17 v := by
  decide +kernel

theorem c0_le_zero_r18 : ∀ v ∈ List.range 125, (carriers 18 v).c0 ≤ zero 18 v := by
  decide +kernel

theorem c0_le_zero_r19 : ∀ v ∈ List.range 124, (carriers 19 v).c0 ≤ zero 19 v := by
  decide +kernel

theorem c0_le_zero_r20 : ∀ v ∈ List.range 123, (carriers 20 v).c0 ≤ zero 20 v := by
  decide +kernel

theorem c0_le_zero_r21 : ∀ v ∈ List.range 122, (carriers 21 v).c0 ≤ zero 21 v := by
  decide +kernel

theorem c0_le_zero_r22 : ∀ v ∈ List.range 121, (carriers 22 v).c0 ≤ zero 22 v := by
  decide +kernel

theorem c0_le_zero_r23 : ∀ v ∈ List.range 120, (carriers 23 v).c0 ≤ zero 23 v := by
  decide +kernel

theorem c0_le_zero_r24 : ∀ v ∈ List.range 119, (carriers 24 v).c0 ≤ zero 24 v := by
  decide +kernel

theorem c0_le_zero_r25 : ∀ v ∈ List.range 118, (carriers 25 v).c0 ≤ zero 25 v := by
  decide +kernel

theorem c0_le_zero_r26 : ∀ v ∈ List.range 117, (carriers 26 v).c0 ≤ zero 26 v := by
  decide +kernel

theorem c0_le_zero_r27 : ∀ v ∈ List.range 116, (carriers 27 v).c0 ≤ zero 27 v := by
  decide +kernel

theorem c0_le_zero_r28 : ∀ v ∈ List.range 115, (carriers 28 v).c0 ≤ zero 28 v := by
  decide +kernel

theorem c0_le_zero_r29 : ∀ v ∈ List.range 114, (carriers 29 v).c0 ≤ zero 29 v := by
  decide +kernel

theorem c0_le_zero_r30 : ∀ v ∈ List.range 113, (carriers 30 v).c0 ≤ zero 30 v := by
  decide +kernel

theorem c0_le_zero_r31 : ∀ v ∈ List.range 112, (carriers 31 v).c0 ≤ zero 31 v := by
  decide +kernel

/-- Every carrier's `c0` is bounded by the table entry at its own cell. -/
theorem c0_le_zero (r v : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 31) (h3 : r + v ≤ 142) :
    (carriers r v).c0 ≤ zero r v := by
  interval_cases r
  · exact c0_le_zero_r1 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r2 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r3 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r4 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r5 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r6 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r7 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r8 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r9 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r10 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r11 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r12 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r13 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r14 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r15 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r16 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r17 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r18 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r19 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r20 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r21 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r22 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r23 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r24 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r25 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r26 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r27 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r28 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r29 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r30 v (List.mem_range.mpr (by omega))
  · exact c0_le_zero_r31 v (List.mem_range.mpr (by omega))

/-- `ZeroAt` follows from the cell bound and superadditivity — no split enumeration. -/
theorem zeroAt_of_algebra (R V : ℕ) (hR : 1 ≤ R) (hR30 : R ≤ 31) (hRV : R + V ≤ 142) :
    ZeroAt carriers R V := by
  intro r hr v hv hrpos hfit
  have hrR : r < R + 1 := List.mem_range.mp hr
  have hvV : v < V + 1 := List.mem_range.mp hv
  by_cases hlt : r < R
  · have hb : 1 ≤ R - r := by omega
    have hs := zero_superadd r (R - r) v (V - v) hrpos hb (by omega) (by omega)
    rw [show r + (R - r) = R by omega, show v + (V - v) = V by omega] at hs
    exact le_trans (Nat.add_le_add_right
      (c0_le_zero r v hrpos (by omega) (by omega)) _) hs
  · have hrE : r = R := by omega
    have hvE : v = V := by rcases hfit with h | h <;> omega
    subst hrE; subst hvE
    rw [show r - r = 0 by omega, show v - v = 0 by omega,
        show zero 0 0 = 0 from rfl, Nat.add_zero]
    exact c0_le_zero r v hrpos (by omega) (by omega)

end ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

