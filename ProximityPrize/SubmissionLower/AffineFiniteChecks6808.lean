import ProximityPrize.SubmissionLower.AffineSingleBridge6808
import ProximityPrize.SubmissionLower.BoundaryTailThresholdData6808
import ProximityPrize.SubmissionLower.BoundaryTailLedgerData6808
namespace ProximityPrize.SubmissionLower.AffineFiniteChecks6808
set_option autoImplicit false
def SingleAt (r v : ℕ) : Prop := AffineSingleData6808.Valid r v ∧ AffineSingleBridge6808.RateAt r v
instance (r v : ℕ) : Decidable (SingleAt r v) := by unfold SingleAt; infer_instance
def PhaseAt (r v : ℕ) : Prop := Lower80830.PhaseChecks.PrefixAt r v ∧ Lower80830.PhaseChecks.RunsAt r v
instance (r v : ℕ) : Decidable (PhaseAt r v) := by unfold PhaseAt; infer_instance
def ThresholdAt (r v : ℕ) : Prop := ∀ j ∈ List.range 10, Lower80830.CompressedData.zowi r v j
instance (r v : ℕ) : Decidable (ThresholdAt r v) := by unfold ThresholdAt; infer_instance
abbrev LedgerAt := Lower80830.LedgerData.At
theorem range_join {P : ℕ → Prop} (start n m : ℕ)
    (hl : ∀ i ∈ List.range n, P (start + i))
    (hr : ∀ i ∈ List.range m, P (start + n + i)) :
    ∀ i ∈ List.range (n + m), P (start + i) := by
  intro i hi
  have hi' := List.mem_range.mp hi
  by_cases h : i < n
  · exact hl i (List.mem_range.mpr h)
  · have hh := hr (i - n) (List.mem_range.mpr (by omega))
    simpa only [show start + n + (i - n) = start + i by omega] using hh

end ProximityPrize.SubmissionLower.AffineFiniteChecks6808
