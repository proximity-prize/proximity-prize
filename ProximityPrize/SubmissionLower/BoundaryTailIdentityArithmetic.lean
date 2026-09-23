import ProximityPrize.SubmissionLower.BoundaryTailIdentity
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

open RCN095 RCN146
open Lower80788.FixedStage
open Lower80788.HybridIdentityC2

def newNormal (f : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed f (reducedABS a b s)
    (rationalABS a b s + 131071 • unitAllFlag)

def newCost (f : FlagDegree) (a b s : ℕ) : ℕ :=
  newNormal f a b s + 65539 * flagMixed f (mfibABS a b s) (mcutABS a b s)

end ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic
