import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

/- The ordinary branch covers 22884 cells. A single fixed A74/2773
source covers the other 2576. Every receipt below is checked by Lean. -/
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

def quotientD (c : Cell) : ℕ := 13456530 - (131071 * ylo c - r c) - 50775
def quotientT (c : Cell) : ℕ := 2773 - tlo c
def quotientYS (c : Cell) : ℕ := 102 - ylo c
def quotientS (c : Cell) : ℕ := 22 - r c
def quotientCost (c : Cell) : ℕ :=
  LocatorFixed.equationCost (quotientD c) (quotientT c) (quotientYS c) (quotientS c)
def bandCost (c : Cell) : ℕ :=
  50775 * LocatorLowQuotient.channelCount (quotientT c) (quotientYS c) (quotientS c)

def OrdinaryFits (c : Cell) : Prop :=
  ordinaryCost c + gridRestCost c ≤ 269000000000000000
instance (c : Cell) : Decidable (OrdinaryFits c) :=
  inferInstanceAs (Decidable (ordinaryCost c + gridRestCost c ≤ 269000000000000000))

def Receipt (c : Cell) : Prop := Valid c →
  OrdinaryFits c ∨ (bandCost c < 38932026630 ∧
    quotientCost c + gridRestCost c ≤ 269000000000000000)
instance (c : Cell) : Decidable (Receipt c) :=
  inferInstanceAs (Decidable (Valid c →
    OrdinaryFits c ∨ (bandCost c < 38932026630 ∧
      quotientCost c + gridRestCost c ≤ 269000000000000000)))

theorem receipt_0 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((0 : Fin 8), yi, ti) := by decide

theorem receipt_1 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((1 : Fin 8), yi, ti) := by decide

theorem receipt_2 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((2 : Fin 8), yi, ti) := by decide

theorem receipt_3 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((3 : Fin 8), yi, ti) := by decide

theorem receipt_4 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((4 : Fin 8), yi, ti) := by decide

theorem receipt_5 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((5 : Fin 8), yi, ti) := by decide

theorem receipt_6 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((6 : Fin 8), yi, ti) := by decide

theorem receipt_7 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((7 : Fin 8), yi, ti) := by decide

theorem receipt (c : Cell) : Receipt c := by
  rcases c with ⟨ri, yi, ti⟩
  fin_cases ri
  · exact receipt_0 yi ti
  · exact receipt_1 yi ti
  · exact receipt_2 yi ti
  · exact receipt_3 yi ti
  · exact receipt_4 yi ti
  · exact receipt_5 yi ti
  · exact receipt_6 yi ti
  · exact receipt_7 yi ti

def chosenCost (c : Cell) : ℕ :=
  if OrdinaryFits c then ordinaryCost c else quotientCost c

theorem chosenCost_with_rest (c : Cell) (hv : Valid c) :
    chosenCost c + gridRestCost c ≤ 269000000000000000 := by
  by_cases h : OrdinaryFits c
  · rw [chosenCost, if_pos h]
    exact h
  · simpa only [chosenCost, if_neg h] using ((receipt c hv).resolve_left h).2

theorem band_lt (c : Cell) (hv : Valid c) (ho : ¬ OrdinaryFits c) :
    bandCost c < 38932026630 := ((receipt c hv).resolve_left ho).1

theorem quotient_caps (c : Cell) (hv : Valid c) :
    131072 ≤ quotientD c ∧ quotientD c ≤ 12488265 ∧
    1 ≤ quotientS c ∧ quotientS c ≤ quotientYS c ∧
    quotientYS c ≤ quotientT c ∧ 2 ≤ quotientYS c ∧
    quotientS c ≤ 15 ∧ quotientYS c ≤ 95 ∧ quotientT c ≤ 10000 := by
  have hr := c.1.isLt
  have ht := c.2.2.isLt
  have hy := hv.1
  dsimp [r, ylo] at hy
  simp only [quotientD, quotientT, quotientYS, quotientS, r, ylo, tlo]
  omega

end ProximityPrize.SubmissionLower.LocatorReplacementData
