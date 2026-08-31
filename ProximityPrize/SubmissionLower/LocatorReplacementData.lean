import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorRateCover
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
open RCN260
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
private abbrev prime:ℕ:=2130706433
private abbrev bound:ℕ:=271423674026155232
def quotient95D (c:Cell):ℕ:=17266820 - (131071 * ylo c - r c) - 50686
def quotient95T (c:Cell):ℕ:=3200 - tlo c
def quotient95YS (c:Cell):ℕ:=131 - ylo c
def quotient95S (c:Cell):ℕ:=29 - r c
def band95 (c:Cell):ℕ :=
  50686 * LocatorLowQuotient.channelCount
    (quotient95T c) (quotient95YS c) (quotient95S c)
def quotient72D (c:Cell):ℕ:=13086432 - (131071 * ylo c - r c) - 50686
def quotient72T (c:Cell):ℕ:=24000 - tlo c
def quotient72YS (c:Cell):ℕ:=99 - ylo c
def quotient72S (c:Cell):ℕ:=21 - r c
def band72 (c:Cell):ℕ :=
  50686 * LocatorLowQuotient.channelCount
    (quotient72T c) (quotient72YS c) (quotient72S c)
def quotient126D (c:Cell):ℕ:=22901256 - (131071 * ylo c - r c) - 50686
def quotient126T (c:Cell):ℕ:=2814 - tlo c
def quotient126YS (c:Cell):ℕ:=174 - ylo c
def quotient126S (c:Cell):ℕ:=39 - r c
def band126 (c:Cell):ℕ :=
  50686 * LocatorLowQuotient.channelCount
    (quotient126T c) (quotient126YS c) (quotient126S c)
def pair95 (c:Cell):UnequalParameters :=
  ⟨262144, 131071, 181756, min (yhi c) (thi c), r c, thi c,
    quotient95YS c, quotient95S c, quotient95T c⟩
def pair72 (c:Cell):UnequalParameters :=
  ⟨262144, 131071, 181756, min (yhi c) (thi c), r c, thi c,
    quotient72YS c, quotient72S c, quotient72T c⟩
def pair126 (c:Cell):UnequalParameters :=
  ⟨262144, 131071, 181756, min (yhi c) (thi c), r c, thi c,
    quotient126YS c, quotient126S c, quotient126T c⟩
def pair95Cost (c:Cell):ℕ:=(pair95 c).regularCountCap
def pair72Cost (c:Cell):ℕ:=(pair72 c).regularCountCap
def pair126Cost (c:Cell):ℕ:=(pair126 c).regularCountCap
def RateFits (c:Cell):Prop :=
  2184 * LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c)) ≤ bound * r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2184 (yhi c) (r c)) ≤ bound
instance (c:Cell):Decidable (RateFits c):=by
  unfold RateFits
  infer_instance
def OrdinaryFits (c:Cell):Prop:=ordinaryCost c + gridRestCost c ≤ bound
instance (c:Cell):Decidable (OrdinaryFits c):=by
  unfold OrdinaryFits
  infer_instance
def Special (c:Cell):Prop :=
  c.1.val = 9 ∧ c.2.1.val = 9 ∧ c.2.2.val = 10
instance (c:Cell):Decidable (Special c):=by
  unfold Special
  infer_instance
theorem special_coordinates (c:Cell) (h:Special c) :
    r c = 10 ∧ ylo c = 46 ∧ tlo c = 1280:=by
  rcases h with ⟨hr, hy, ht⟩
  simp only [r, ylo, tlo]
  omega
def Coprime95 (c:Cell):Prop :=
  quotient95T c < tlo c ∨ quotient95YS c < ylo c ∨ quotient95S c < r c
instance (c:Cell):Decidable (Coprime95 c):=by
  unfold Coprime95
  infer_instance
def Coprime72 (c:Cell):Prop :=
  quotient72T c < tlo c ∨ quotient72YS c < ylo c ∨ quotient72S c < r c
instance (c:Cell):Decidable (Coprime72 c):=by
  unfold Coprime72
  infer_instance
def Coprime126 (c:Cell):Prop :=
  quotient126T c < tlo c ∨ quotient126YS c < ylo c ∨ quotient126S c < r c
instance (c:Cell):Decidable (Coprime126 c):=by
  unfold Coprime126
  infer_instance
def PairGates (P:UnequalParameters):Prop :=
  1 ≤ P.leftR ∧ P.leftY < prime ∧ P.leftR < prime ∧ P.leftZ < prime ∧
    P.mixedCost.y < prime ∧ P.mixedCost.r < prime ∧ P.mixedCost.z < prime
instance (P:UnequalParameters):Decidable (PairGates P):=by
  unfold PairGates
  infer_instance
def Pair95Fits (c:Cell):Prop :=
  band95 c < 129230045740 ∧ Coprime95 c ∧ PairGates (pair95 c) ∧
    pair95Cost c + gridRestCost c ≤ bound
instance (c:Cell):Decidable (Pair95Fits c):=by
  unfold Pair95Fits
  infer_instance
def Pair72Fits (c:Cell):Prop :=
  band72 c < 658852027658 ∧ Coprime72 c ∧ PairGates (pair72 c) ∧
    pair72Cost c + gridRestCost c ≤ bound
instance (c:Cell):Decidable (Pair72Fits c):=by
  unfold Pair72Fits
  infer_instance
def Pair126Fits (c:Cell):Prop :=
  band126 c < 241401798610 ∧ Coprime126 c ∧ PairGates (pair126 c) ∧
    pair126Cost c + gridRestCost c ≤ bound
instance (c:Cell):Decidable (Pair126Fits c):=by
  unfold Pair126Fits
  infer_instance
def Receipt (c:Cell):Prop:=Valid c →
  RateFits c ∨ OrdinaryFits c ∨ Pair95Fits c ∨ Pair72Fits c ∨
    Pair126Fits c ∨ Special c
instance (c:Cell):Decidable (Receipt c):=by
  unfold Receipt
  infer_instance
theorem receipt_0:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((0:Fin 16), yi, ti):=by decide
theorem receipt_1:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((1:Fin 16), yi, ti):=by decide
theorem receipt_2:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((2:Fin 16), yi, ti):=by decide
theorem receipt_3:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((3:Fin 16), yi, ti):=by decide
theorem receipt_4:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((4:Fin 16), yi, ti):=by decide
theorem receipt_5:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((5:Fin 16), yi, ti):=by decide
theorem receipt_6:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((6:Fin 16), yi, ti):=by decide
theorem receipt_7:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((7:Fin 16), yi, ti):=by decide
theorem receipt_8:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((8:Fin 16), yi, ti):=by decide
theorem receipt_9:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((9:Fin 16), yi, ti):=by decide
theorem receipt_10:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((10:Fin 16), yi, ti):=by decide
theorem receipt_11:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((11:Fin 16), yi, ti):=by decide
theorem receipt_12:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((12:Fin 16), yi, ti):=by decide
theorem receipt_13:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((13:Fin 16), yi, ti):=by decide
theorem receipt_14:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((14:Fin 16), yi, ti):=by decide
theorem receipt_15:∀ yi:Fin 19, ∀ ti:Fin 18,
    Receipt ((15:Fin 16), yi, ti):=by decide
theorem receipt (c:Cell):Receipt c:=by
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
  · exact receipt_15 yi ti
def chosenCost (c:Cell):ℕ :=
  if OrdinaryFits c then ordinaryCost c
  else if Pair95Fits c then pair95Cost c
  else if Pair72Fits c then pair72Cost c else pair126Cost c
theorem chosenCost_with_rest (c:Cell) (hv:Valid c) (hnr:¬ RateFits c)
    (hspecial:¬ Special c) :
    chosenCost c + gridRestCost c ≤ bound:=by
  have hroutes:=(receipt c hv).resolve_left hnr
  by_cases ho:OrdinaryFits c
  · have ho':ordinaryCost c + gridRestCost c ≤ bound:=by
      simpa only [OrdinaryFits] using ho
    rw [chosenCost, if_pos ho]
    exact ho'
  · have hpairs:=hroutes.resolve_left ho
    by_cases h95:Pair95Fits c
    · simpa only [chosenCost, if_neg ho, if_pos h95] using h95.2.2.2
    · have hpairs':=hpairs.resolve_left h95
      by_cases h72:Pair72Fits c
      · simpa only [chosenCost, if_neg ho, if_neg h95, if_pos h72] using h72.2.2.2
      · have h126:Pair126Fits c :=
          (hpairs'.resolve_left h72).resolve_right hspecial
        simpa only [chosenCost, if_neg ho, if_neg h95, if_neg h72] using h126.2.2.2
end ProximityPrize.SubmissionLower.LocatorReplacementData
