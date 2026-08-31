import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

def quotientD (c : Cell) : ℕ := 14002065 - (131071 * ylo c - r c) - 50775
def quotientT (c : Cell) : ℕ := 2567 - tlo c
def quotientYS (c : Cell) : ℕ := 106 - ylo c
def quotientS (c : Cell) : ℕ := 23 - r c
def quotientCost (c : Cell) : ℕ :=
  LocatorFixed.equationCost (quotientD c) (quotientT c) (quotientYS c) (quotientS c)
def bandCost (c : Cell) : ℕ :=
  50775 * LocatorLowQuotient.channelCount (quotientT c) (quotientYS c) (quotientS c)

def OrdinaryFits (c : Cell) : Prop :=
  ordinaryCost c + gridRestCost c ≤ 271500000000000000
instance (c : Cell) : Decidable (OrdinaryFits c) :=
  inferInstanceAs (Decidable (ordinaryCost c + gridRestCost c ≤ 271500000000000000))

def Receipt (c : Cell) : Prop := Valid c →
  OrdinaryFits c ∨ (bandCost c < 38456280382 ∧
    quotientCost c + gridRestCost c ≤ 271500000000000000)
instance (c : Cell) : Decidable (Receipt c) :=
  inferInstanceAs (Decidable (Valid c →
    OrdinaryFits c ∨ (bandCost c < 38456280382 ∧
      quotientCost c + gridRestCost c ≤ 271500000000000000)))

end ProximityPrize.SubmissionLower.LocatorReplacementData
