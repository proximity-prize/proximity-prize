/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs
import ProximityPrize.SubmissionLower.Koala6831MovingFixedRooms

namespace ProximityPrize.SubmissionLower.Koala6831MovingPaid

open RCN095 RCN130 RCN275 LocatorFactorAggregate
open Koala6831Moving Koala6831MovingLedger Koala6831MovingSources Koala6831MovingPairIncidence

def agreementScale : ℕ := 9055167546

theorem agreementScale_eq : agreementScale = 181078 * (181078 - 131071) := by decide +kernel
theorem agreementScale_pos : 0 < agreementScale := by decide +kernel

def primaryIncoming : FlagDegree := ⟨41464, 325, 93⟩
def secondRoomIncoming : FlagDegree := ⟨15120, 179, 52⟩

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
  scaledPairFlag (stageSupport incoming hpos) 262144 131071 181078 81066

def stagePrice (incoming : FlagDegree) (hpos : 0 < incoming.all) (s : Stage) (gain : ℕ) : ℕ :=
  flagMixed incoming (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale

def fixedRoomPrice₁ : ℕ := stagePrice primaryIncoming (by decide +kernel) Stage.room1 Stage.room1.roomOrder
def fixedRoomPrice₂ : ℕ := stagePrice secondRoomIncoming (by decide +kernel) Stage.room2 Stage.room2.roomOrder

def fixedRoomCredit₁ (final : FlagDegree) : ℕ :=
  flagMixed (creditFlag final) (stagePartnerFlag Stage.room1 Stage.room1.roomOrder)
    (stageScaledCut primaryIncoming (by decide +kernel)) / agreementScale

def fixedRoomCredit₂ (final : FlagDegree) : ℕ :=
  flagMixed (creditFlag final) (stagePartnerFlag Stage.room2 Stage.room2.roomOrder)
    (stageScaledCut secondRoomIncoming (by decide +kernel)) / agreementScale

theorem fixedRoomPrice₁_value : fixedRoomPrice₁ = 16109414926486663 := by decide +kernel
theorem fixedRoomPrice₂_value : fixedRoomPrice₂ = 8723255558342297 := by decide +kernel

end ProximityPrize.SubmissionLower.Koala6831MovingPaid

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
