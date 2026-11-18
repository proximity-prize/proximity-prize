/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs
import ProximityPrize.SubmissionLower.Koala6831MovingFixedRooms
import ProximityPrize.SubmissionLower.Mid6833K6833FlowSchedule

namespace ProximityPrize.SubmissionLower.K6833FlowPaid

open RCN095 RCN130 RCN275 LocatorFactorAggregate
open Koala6831Moving Koala6831MovingLedger K6833FlowSources Koala6831MovingPairIncidence

def agreementScale : ℕ := 9052856796

theorem agreementScale_eq : agreementScale = 181068 * (181068 - 131071) := by decide +kernel
theorem agreementScale_pos : 0 < agreementScale := by decide +kernel

def primaryIncoming : FlagDegree := ⟨44944, 342, 98⟩


def stageSupport (incoming : FlagDegree) (hpos : 0 < incoming.all) :
    ResidualSupportParameters where
  s := incoming.all
  ys := max 2 (middle incoming)
  total := max 2 (total incoming)
  one_le_s := hpos
  s_le_ys := (Nat.le_add_left _ _).trans (le_max_right _ _)
  ys_le_total := max_le_max_left _ (by unfold middle total; omega)
  two_le_ys := le_max_left _ _

def stagePartnerFlag (s : Stage) (gain : ℕ) : FlagDegree :=
  flagFromCaps (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap

theorem stagePartnerFlag_cumulative (s : Stage) (gain : ℕ) :
    (stagePartnerFlag s gain).all = s.numbers.slopeCap ∧
    middle (stagePartnerFlag s gain) = s.numbers.middleCap ∧
    total (stagePartnerFlag s gain) = s.numbers.totalCap + gain :=
  flagFromCaps_cumulative _ _ _ (by cases s <;> decide +kernel)
    ((show s.numbers.middleCap ≤ s.numbers.totalCap by cases s <;> decide +kernel).trans
      (Nat.le_add_right _ _))

def stageScaledCut (incoming : FlagDegree) (hpos : 0 < incoming.all) : FlagDegree :=
  scaledPairFlag (stageSupport incoming hpos) 262144 131071 181068 81076

def stagePrice (incoming : FlagDegree) (hpos : 0 < incoming.all) (s : Stage) (gain : ℕ) : ℕ :=
  flagMixed incoming (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale

end ProximityPrize.SubmissionLower.K6833FlowPaid
