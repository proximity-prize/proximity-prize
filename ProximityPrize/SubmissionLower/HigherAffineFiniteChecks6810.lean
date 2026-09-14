import ProximityPrize.SubmissionLower.HigherAffineRateBridge6810
import ProximityPrize.SubmissionLower.HigherThresholdData6810
import ProximityPrize.SubmissionLower.HigherLedgerData6810
namespace ProximityPrize.SubmissionLower.HigherAffineFiniteChecks6810
set_option autoImplicit false
def SingleAt (r v : ℕ) : Prop := HigherAffineSingleData6810.Valid r v ∧ HigherAffineRateBridge6810.RateAt r v
instance (r v : ℕ) : Decidable (SingleAt r v) := by unfold SingleAt; infer_instance
def PhaseAt (r v : ℕ) : Prop := Lower80850.PhaseChecks.PrefixAt r v ∧ Lower80850.PhaseChecks.RunsAt r v
instance (r v : ℕ) : Decidable (PhaseAt r v) := by unfold PhaseAt; infer_instance
def ThresholdAt (r v : ℕ) : Prop := ∀ j ∈ List.range 10, Lower80850.CompressedData.zowi r v j
instance (r v : ℕ) : Decidable (ThresholdAt r v) := by unfold ThresholdAt; infer_instance
abbrev LedgerAt := Lower80850.LedgerData.At
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

end ProximityPrize.SubmissionLower.HigherAffineFiniteChecks6810
