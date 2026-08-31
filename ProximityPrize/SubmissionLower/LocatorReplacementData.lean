import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorRateCover
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5

/-! Exact finite certificate for the 67.60 regular-factor cover.

Every valid 128-by-4 cell is handled by one of four routes: the global
cost/total rate, the ordinary first-factor cost, or a coprime regular-left
intersection with one of the two already selected auxiliary kernels.  The
pair route pays no singular cost for the quotient. -/
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
open RCN260
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private abbrev prime : ℕ := 2130706433
private abbrev bound : ℕ := 267000000000000000

def quotient95D (c : Cell) : ℕ := 17269670 - (131071 * ylo c - r c) - 50716
def quotient95T (c : Cell) : ℕ := 2800 - tlo c
def quotient95YS (c : Cell) : ℕ := 131 - ylo c
def quotient95S (c : Cell) : ℕ := 29 - r c
def band95 (c : Cell) : ℕ :=
  50716 * LocatorLowQuotient.channelCount
    (quotient95T c) (quotient95YS c) (quotient95S c)

def quotient72D (c : Cell) : ℕ := 13088592 - (131071 * ylo c - r c) - 50716
def quotient72T (c : Cell) : ℕ := 7000 - tlo c
def quotient72YS (c : Cell) : ℕ := 99 - ylo c
def quotient72S (c : Cell) : ℕ := 21 - r c
def band72 (c : Cell) : ℕ :=
  50716 * LocatorLowQuotient.channelCount
    (quotient72T c) (quotient72YS c) (quotient72S c)

def pair95 (c : Cell) : UnequalParameters :=
  ⟨262144, 131071, 181786, min (yhi c) (thi c), r c, thi c,
    quotient95YS c, quotient95S c, quotient95T c⟩

def pair72 (c : Cell) : UnequalParameters :=
  ⟨262144, 131071, 181786, min (yhi c) (thi c), r c, thi c,
    quotient72YS c, quotient72S c, quotient72T c⟩

def pair95Cost (c : Cell) : ℕ := (pair95 c).regularCountCap
def pair72Cost (c : Cell) : ℕ := (pair72 c).regularCountCap

def RateFits (c : Cell) : Prop :=
  2029 * LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c)) ≤ bound * r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2029 (yhi c) (r c)) ≤ bound

instance (c : Cell) : Decidable (RateFits c) := by
  unfold RateFits
  infer_instance

def OrdinaryFits (c : Cell) : Prop := ordinaryCost c + gridRestCost c ≤ bound
instance (c : Cell) : Decidable (OrdinaryFits c) := by
  unfold OrdinaryFits
  infer_instance

def Coprime95 (c : Cell) : Prop :=
  quotient95T c < tlo c ∨ quotient95YS c < ylo c ∨ quotient95S c < r c
instance (c : Cell) : Decidable (Coprime95 c) := by
  unfold Coprime95
  infer_instance

def Coprime72 (c : Cell) : Prop :=
  quotient72T c < tlo c ∨ quotient72YS c < ylo c ∨ quotient72S c < r c
instance (c : Cell) : Decidable (Coprime72 c) := by
  unfold Coprime72
  infer_instance

def PairGates (P : UnequalParameters) : Prop :=
  1 ≤ P.leftR ∧ P.leftY < prime ∧ P.leftR < prime ∧ P.leftZ < prime ∧
    P.mixedCost.y < prime ∧ P.mixedCost.r < prime ∧ P.mixedCost.z < prime
instance (P : UnequalParameters) : Decidable (PairGates P) := by
  unfold PairGates
  infer_instance

def Pair95Fits (c : Cell) : Prop :=
  band95 c < 104761399990 ∧ Coprime95 c ∧ PairGates (pair95 c) ∧
    pair95Cost c + gridRestCost c ≤ bound
instance (c : Cell) : Decidable (Pair95Fits c) := by
  unfold Pair95Fits
  infer_instance

def Pair72Fits (c : Cell) : Prop :=
  band72 c < 155878194098 ∧ Coprime72 c ∧ PairGates (pair72 c) ∧
    pair72Cost c + gridRestCost c ≤ bound
instance (c : Cell) : Decidable (Pair72Fits c) := by
  unfold Pair72Fits
  infer_instance

def Receipt (c : Cell) : Prop := Valid c →
  RateFits c ∨ OrdinaryFits c ∨ Pair95Fits c ∨ Pair72Fits c
instance (c : Cell) : Decidable (Receipt c) := by
  unfold Receipt
  infer_instance

theorem receipt_0 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((0 : Fin 15), yi, ti) := by decide
theorem receipt_1 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((1 : Fin 15), yi, ti) := by decide
theorem receipt_2 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((2 : Fin 15), yi, ti) := by decide
theorem receipt_3 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((3 : Fin 15), yi, ti) := by decide
theorem receipt_4 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((4 : Fin 15), yi, ti) := by decide
theorem receipt_5 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((5 : Fin 15), yi, ti) := by decide
theorem receipt_6 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((6 : Fin 15), yi, ti) := by decide
theorem receipt_7 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((7 : Fin 15), yi, ti) := by decide
theorem receipt_8 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((8 : Fin 15), yi, ti) := by decide
theorem receipt_9 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((9 : Fin 15), yi, ti) := by decide
theorem receipt_10 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((10 : Fin 15), yi, ti) := by decide
theorem receipt_11 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((11 : Fin 15), yi, ti) := by decide
theorem receipt_12 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((12 : Fin 15), yi, ti) := by decide
theorem receipt_13 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((13 : Fin 15), yi, ti) := by decide
theorem receipt_14 : ∀ yi : Fin 18, ∀ ti : Fin 16,
    Receipt ((14 : Fin 15), yi, ti) := by decide

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
  · exact receipt_8 yi ti
  · exact receipt_9 yi ti
  · exact receipt_10 yi ti
  · exact receipt_11 yi ti
  · exact receipt_12 yi ti
  · exact receipt_13 yi ti
  · exact receipt_14 yi ti

def chosenCost (c : Cell) : ℕ :=
  if OrdinaryFits c then ordinaryCost c
  else if Pair95Fits c then pair95Cost c else pair72Cost c

theorem chosenCost_with_rest (c : Cell) (hv : Valid c) (hnr : ¬ RateFits c) :
    chosenCost c + gridRestCost c ≤ bound := by
  have hroutes := (receipt c hv).resolve_left hnr
  by_cases ho : OrdinaryFits c
  · have ho' : ordinaryCost c + gridRestCost c ≤ bound := by
      simpa only [OrdinaryFits] using ho
    rw [chosenCost, if_pos ho]
    exact ho'
  · have hpairs := hroutes.resolve_left ho
    by_cases h95 : Pair95Fits c
    · simpa only [chosenCost, if_neg ho, if_pos h95] using h95.2.2.2
    · have h72 := hpairs.resolve_left h95
      simpa only [chosenCost, if_neg ho, if_neg h95] using h72.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementData
