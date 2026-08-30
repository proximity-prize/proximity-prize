import ProximityPrize.SubmissionLower.ContactRegularFactorFlag

namespace ProximityPrize.SubmissionLower.ContactRobustFixedMeet

open scoped BigOperators
open ContactInterpolation ContactSelectedSeedDecomposition
open ContactFlagBezout
open ContactRegularFactorFlag

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

structure Profile where
  n : ℕ
  w : ℕ
  agreements : ℕ
  weightedCap : ℕ
  seedTotalCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq, Repr

namespace Profile

def errors (p : Profile) : ℕ := p.n - p.agreements
def gap (p : Profile) : ℕ := p.agreements - p.w

def degreeIncidence (p : Profile) : ℕ :=
  (p.n * p.gap * p.w + p.agreements - 1) / p.agreements

def unitIncidence (p : Profile) : ℕ := p.n - p.w

end Profile

noncomputable section

variable {K : Type} [Field K]

end

end ProximityPrize.SubmissionLower.ContactRobustFixedMeet
