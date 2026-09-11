import ProximityPrize.SubmissionLower.BoundaryTailStrictCorners
import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore BoundaryTailBaseFast BoundaryTailConvexity
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

/-- All numeric facts for one parent cell; the corner theorem supplies every
proper split and the zero receipt follows from its z=0 component. -/
def Cell (R V : ℕ) : Prop :=
  let q := BoundaryTailBaseFastData.row R V
  CorrectAt R V ∧ BaseCheckAt R V ∧ Valid q R V ∧
    ZeroCertificate q R V ∧ strictCornersBool q R V = true

instance (R V : ℕ) : Decidable (Cell R V) := by
  unfold Cell
  infer_instance

-- Keep each row separately kernel checked to bound peak memory.
theorem row1 : ∀ V ∈ List.range 142, Cell 1 V := by decide +kernel
theorem row2 : ∀ V ∈ List.range 141, Cell 2 V := by decide +kernel
theorem row3 : ∀ V ∈ List.range 140, Cell 3 V := by decide +kernel
theorem row4 : ∀ V ∈ List.range 139, Cell 4 V := by decide +kernel
theorem row5 : ∀ V ∈ List.range 138, Cell 5 V := by decide +kernel
theorem row6 : ∀ V ∈ List.range 137, Cell 6 V := by decide +kernel
theorem row7 : ∀ V ∈ List.range 136, Cell 7 V := by decide +kernel
theorem row8 : ∀ V ∈ List.range 135, Cell 8 V := by decide +kernel
theorem row9 : ∀ V ∈ List.range 134, Cell 9 V := by decide +kernel
theorem row10 : ∀ V ∈ List.range 133, Cell 10 V := by decide +kernel
theorem row11 : ∀ V ∈ List.range 132, Cell 11 V := by decide +kernel
theorem row12 : ∀ V ∈ List.range 131, Cell 12 V := by decide +kernel
theorem row13 : ∀ V ∈ List.range 130, Cell 13 V := by decide +kernel
theorem row14 : ∀ V ∈ List.range 129, Cell 14 V := by decide +kernel
theorem row15 : ∀ V ∈ List.range 128, Cell 15 V := by decide +kernel
theorem row16 : ∀ V ∈ List.range 127, Cell 16 V := by decide +kernel
theorem row17 : ∀ V ∈ List.range 126, Cell 17 V := by decide +kernel
theorem row18 : ∀ V ∈ List.range 125, Cell 18 V := by decide +kernel
theorem row19 : ∀ V ∈ List.range 124, Cell 19 V := by decide +kernel
theorem row20 : ∀ V ∈ List.range 123, Cell 20 V := by decide +kernel
theorem row21 : ∀ V ∈ List.range 122, Cell 21 V := by decide +kernel
theorem row22 : ∀ V ∈ List.range 121, Cell 22 V := by decide +kernel
theorem row23 : ∀ V ∈ List.range 120, Cell 23 V := by decide +kernel
theorem row24 : ∀ V ∈ List.range 119, Cell 24 V := by decide +kernel
theorem row25 : ∀ V ∈ List.range 118, Cell 25 V := by decide +kernel
theorem row26 : ∀ V ∈ List.range 117, Cell 26 V := by decide +kernel
theorem row27 : ∀ V ∈ List.range 116, Cell 27 V := by decide +kernel
theorem row28 : ∀ V ∈ List.range 115, Cell 28 V := by decide +kernel
theorem row29 : ∀ V ∈ List.range 114, Cell 29 V := by decide +kernel
theorem row30 : ∀ V ∈ List.range 113, Cell 30 V := by decide +kernel
theorem row31 : ∀ V ∈ List.range 112, Cell 31 V := by decide +kernel

theorem all (R V : ℕ) (hR : 1 ≤ R) (hRmax : R ≤ 31) (hRV : R+V ≤ 142) :
    Cell R V := by
  interval_cases R
  · exact row1 V (List.mem_range.mpr (by omega))
  · exact row2 V (List.mem_range.mpr (by omega))
  · exact row3 V (List.mem_range.mpr (by omega))
  · exact row4 V (List.mem_range.mpr (by omega))
  · exact row5 V (List.mem_range.mpr (by omega))
  · exact row6 V (List.mem_range.mpr (by omega))
  · exact row7 V (List.mem_range.mpr (by omega))
  · exact row8 V (List.mem_range.mpr (by omega))
  · exact row9 V (List.mem_range.mpr (by omega))
  · exact row10 V (List.mem_range.mpr (by omega))
  · exact row11 V (List.mem_range.mpr (by omega))
  · exact row12 V (List.mem_range.mpr (by omega))
  · exact row13 V (List.mem_range.mpr (by omega))
  · exact row14 V (List.mem_range.mpr (by omega))
  · exact row15 V (List.mem_range.mpr (by omega))
  · exact row16 V (List.mem_range.mpr (by omega))
  · exact row17 V (List.mem_range.mpr (by omega))
  · exact row18 V (List.mem_range.mpr (by omega))
  · exact row19 V (List.mem_range.mpr (by omega))
  · exact row20 V (List.mem_range.mpr (by omega))
  · exact row21 V (List.mem_range.mpr (by omega))
  · exact row22 V (List.mem_range.mpr (by omega))
  · exact row23 V (List.mem_range.mpr (by omega))
  · exact row24 V (List.mem_range.mpr (by omega))
  · exact row25 V (List.mem_range.mpr (by omega))
  · exact row26 V (List.mem_range.mpr (by omega))
  · exact row27 V (List.mem_range.mpr (by omega))
  · exact row28 V (List.mem_range.mpr (by omega))
  · exact row29 V (List.mem_range.mpr (by omega))
  · exact row30 V (List.mem_range.mpr (by omega))
  · exact row31 V (List.mem_range.mpr (by omega))

theorem receipt : BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap BoundaryTailBaseData.cap := by
  apply receipt_of_checks carriers runs
  · intro R V hR hRmax hRV
    exact (all R V hR hRmax hRV).1
  · intro R V hR hRmax hRV
    rcases all R V hR hRmax hRV with ⟨_, _, _, hz, hs⟩
    exact zeroAtFast_sound R V (zeroAtFast_of_strict _ R V
      (strictCornersBool_sound _ R V hs) hz)
  · intro R V hR hRmax hRV
    rcases all R V hR hRmax hRV with ⟨_, _, hv, _, hs⟩
    exact strictAtFast_sound _ R V hv (strictCornersBool_sound _ R V hs)
  · intro R V hR hRmax hRV
    exact (all R V hR hRmax hRV).2.1

theorem phaseReceipt : BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero
    BoundaryTailStrictData.cap (Lower80811.PhaseSemantics.phaseCap 0) := by
  convert receipt using 1
  funext p
  rfl

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
