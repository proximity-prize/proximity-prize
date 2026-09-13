import ProximityPrize.SubmissionLower.BoundaryTailPhaseRuns6807
import ProximityPrize.SubmissionLower.BoundaryTailBaseOracle6807
import ProximityPrize.SubmissionLower.BoundaryTailRouting6807

namespace ProximityPrize.SubmissionLower.Lower80820.PhaseSemantics
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN130 RCN140 RCN238 RCN266 RCN275 LocatorFactorAggregate
open LocatorBatchProductRoute
open LocatorPhase6800Oracle (sumFlag)
open LocatorBatchPhase6800 (regularAggregateFlag)
open Lower80820.BatchPhase
set_option autoImplicit false
noncomputable section
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

/-- The base step consumes the actual per-factor cap already established by
BoundaryTailBase6807.regular_factor_count (or its carrier specialization). Its
remaining assumptions are precisely the generated arithmetic receipts. -/
theorem stateLocalRegularBoundOn_of_base
    {zero : ℕ → ℕ → ℕ} {split base : FlagDegree → ℕ}
    (receipt : BoundaryTailBaseOracle6807.Receipt zero split base)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hsingle : ∀ F ∈ ambient, (regularSeeds H selected Gamma F).card ≤
      BoundaryTailBase6807.cap (regularCumulativeFlag H F)) :
    StateLocalRegularBoundOn H selected Gamma ambient base := by
  classical
  intro A hAambient hs hy ht
  exact receipt.sum_count_le A (regularCumulativeFlag H)
    (fun F => (regularSeeds H selected Gamma F).card)
    (fun F _ => Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
    hs hy ht (fun F hF => hsingle F (hAambient hF))

end
end ProximityPrize.SubmissionLower.Lower80820.PhaseSemantics
