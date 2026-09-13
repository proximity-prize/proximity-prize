import ProximityPrize.SubmissionLower.BoundaryTailBaseFast6807
import ProximityPrize.SubmissionLower.BoundaryTailLedgerData6807
import ProximityPrize.SubmissionLower.BoundaryTailThresholdData6807
namespace ProximityPrize.SubmissionLower.BoundaryTailFiniteChecks6807
open BoundaryTailBaseFast6807 BoundaryTailBaseChecksData6807
open Lower80820.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def GeometryAt (r v : ℕ) : Prop :=
  CorrectAt r v ∧ BaseCheckAt r v ∧
  Valid (BoundaryTailBaseFastData6807.row r v) r v ∧
  ZeroCertificate (BoundaryTailBaseFastData6807.row r v) r v
instance (r v : ℕ) : Decidable (GeometryAt r v) := by unfold GeometryAt; infer_instance

def StrictAt (r v : ℕ) : Prop :=
  StrictAtFast (BoundaryTailBaseFastData6807.row r v) r v
instance (r v : ℕ) : Decidable (StrictAt r v) := by unfold StrictAt; infer_instance

def ThresholdAt (r v : ℕ) : Prop :=
  ∀ j ∈ List.range 10, Lower80820.CompressedData.zowi r v j
instance (r v : ℕ) : Decidable (ThresholdAt r v) := by unfold ThresholdAt; infer_instance

def PhaseAt (r v : ℕ) : Prop := PrefixAt r v ∧ RunsAt r v
instance (r v : ℕ) : Decidable (PhaseAt r v) := by unfold PhaseAt; infer_instance

def LedgerAt (r v : ℕ) : Prop := Lower80820.LedgerData.At r v
instance (r v : ℕ) : Decidable (LedgerAt r v) := by unfold LedgerAt; infer_instance
end ProximityPrize.SubmissionLower.BoundaryTailFiniteChecks6807
