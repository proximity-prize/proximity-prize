import ProximityPrize.SubmissionLower.Koala6844ReceiptsChannels
import ProximityPrize.SubmissionLower.Koala6844ReceiptsStageExit
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPhysicalPair

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle

def Flag.toFlagDegree (f : Flag) : FlagDegree :=
  ⟨f.t-f.y,f.y-f.r,f.r⟩

def bandSourceNumbers (source : Flag) (gap : Nat) : SourceNumbers :=
  ⟨source.t,source.y,source.r,gap⟩

theorem Flag.toFlagDegree_middle (f : Flag) (h : f.ordered) :
    middle f.toFlagDegree = f.y := by
  have hr := h.1
  change f.y - f.r + f.r = f.y
  omega

theorem Flag.toFlagDegree_total (f : Flag) (h : f.ordered) :
    total f.toFlagDegree = f.t := by
  have hr := h.1
  have hy := h.2
  change (f.t - f.y) + (f.y - f.r) + f.r = f.t
  omega

theorem bandCovers_iff_geometric (source target : Flag) (gap : Nat) (h : target.ordered) :
    bandCovers source target gap = true ↔
      geometricGate flowWidth (bandSourceNumbers source gap) target.toFlagDegree := by
  unfold bandCovers geometricGate geometricBand
  rw [decide_eq_true_eq,fastPowerBandBudget_eq]
  simp only [LocatorPhase6800Oracle.SourceNumbers.fuel,bandSourceNumbers,bandFuel,
    Flag.toFlagDegree_middle target h,Flag.toFlagDegree_total target h]
  have hFuel : min (source.r / target.r) (min (source.y / target.y) (source.t / target.t)) =
      min (source.t / target.t) (min (source.y / target.y) (source.r / target.r)) := by
    omega
  rw [hFuel]
  rfl

end ProximityPrize.SubmissionLower.Koala6844Receipts
