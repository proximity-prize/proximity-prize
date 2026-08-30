import ProximityPrize.SubmissionLower.ContactNearPencil6600Arithmetic

namespace ProximityPrize.SubmissionLower.ContactParameters

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def prime : ℕ := 2130706433

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

end ProximityPrize.SubmissionLower.ContactParameters
