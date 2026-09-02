import ProximityPrize.SubmissionLower.LocatorFactorAggregate

/-! Definition-only hybrid second-surface cost API for generated grid receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open RCN095 LocatorFactorAggregate

/-- Sharp first tail at `d = 131072`. -/
def sharpTail (p : FlagDegree) : FlagDegree :=
  ⟨2 * (padT p - padY p) * 131072,
    1 + (2 * (padY p - padS p) - 1) * 131072,
    (2 * padS p - 1) * 131072⟩

def rationalFlag (p : FlagDegree) : FlagDegree :=
  ⟨131072 * (padT p - padY p) + 2 * (padT p - padY p),
    131072 * (padY p - padS p - 1) + 2 * (padY p - padS p - 1) + 2,
    131072 * (padS p - 2) + 2 * (padS p - 2) + 3⟩

def hybridCoordinate (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 65536, 196608⟩

def movingFiber (p : FlagDegree) : FlagDegree :=
  ⟨padT p - padY p, padY p - padS p, padS p + 1⟩

def movingCut (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 131072, 262144⟩

def hybridCost (p : FlagDegree) : ℕ :=
  flagMixed p (sharpTail p) (hybridCoordinate p) +
    131072 * flagMixed p (movingFiber p) (movingCut p)

end ProximityPrize.SubmissionLower.LocatorHybridCost
