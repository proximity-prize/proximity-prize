import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorRateCover
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open scoped BigOperators
open LocatorReplacementGrid RCN260 RCN302 RCN180
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
private abbrev prime:ℕ:=2130706433
private abbrev bound:ℕ:=271823484960074903
private abbrev delta:ℕ:=50657
abbrev GridCell:=LocatorReplacementGrid.Cell

def channelMultiplicity (ys ss:ℕ):ℕ:=
  ∑ u ∈ Finset.range (ys+1), (min ss u+1)
def channelMoment (ys ss:ℕ):ℕ:=
  ∑ u ∈ Finset.range (ys+1),u*(min ss u+1)
def suggestedLength (a debt minimumL Ysrc sourceS:ℕ) (c:GridCell):ℕ:=
  let ft:=max (tlo c) (ylo c)
  let qY:=Ysrc-ylo c
  let qR:=min (sourceS-r c) qY
  let channels:=channelMultiplicity qY qR
  let moment:=channelMoment qY qR
  let slope:=a-delta*channels
  let rhs:=debt-delta*((ft-1)*channels+moment)
  let base:=max minimumL (max (ft+qY) (ft+1))
  if slope=0 then base else max base (rhs/slope+1)

def length72 (c:GridCell):ℕ:=suggestedLength 27213285 92717283934 3408 99 21 c
def length126 (c:GridCell):ℕ:=suggestedLength 378451680 885351026630 2340 174 39 c
def lengthDouble126 (c:GridCell):ℕ:=2*tlo c+1000
def quotient72D (c:GridCell):ℕ:=13084344-(131071*ylo c-r c)-delta
def quotient72T (c:GridCell):ℕ:=length72 c-tlo c
def quotient72YS (c:GridCell):ℕ:=99-ylo c
def quotient72S (c:GridCell):ℕ:=21-r c
def quotient126D (c:GridCell):ℕ:=22897602-(131071*ylo c-r c)-delta
def quotient126T (c:GridCell):ℕ:=length126 c-tlo c
def quotient126YS (c:GridCell):ℕ:=174-ylo c
def quotient126S (c:GridCell):ℕ:=39-r c
def quotientDoubleT (c:GridCell):ℕ:=lengthDouble126 c-tlo c
def quotientDoubleYS (c:GridCell):ℕ:=174-ylo c
def quotientDoubleS (c:GridCell):ℕ:=39-r c
def secondDoubleT (c:GridCell):ℕ:=lengthDouble126 c-2*tlo c
def secondDoubleYS (c:GridCell):ℕ:=174-2*ylo c
def secondDoubleS (c:GridCell):ℕ:=39-2*r c
def band72 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient72T c) (quotient72YS c) (quotient72S c)
def band126 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient126T c) (quotient126YS c) (quotient126S c)
def bandDoubleFirst (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotientDoubleT c) (quotientDoubleYS c) (quotientDoubleS c)
def bandDoubleSecond (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (secondDoubleT c) (secondDoubleYS c) (secondDoubleS c)
def sourceGap72 (c:GridCell):ℕ:=
  27213285*length72 c-92717283934
def sourceGap126 (c:GridCell):ℕ:=
  378451680*length126 c-885351026630
def sourceGapDouble126 (c:GridCell):ℕ:=
  378451680*lengthDouble126 c-885351026630
def pair72 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181727,min (yhi c) (thi c),r c,thi c,
    quotient72YS c,quotient72S c,quotient72T c⟩
def pair126 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181727,min (yhi c) (thi c),r c,thi c,
    quotient126YS c,quotient126S c,quotient126T c⟩
def pairDoubleFirst (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181727,min (yhi c) (thi c),r c,thi c,
    quotientDoubleYS c,quotientDoubleS c,quotientDoubleT c⟩
def pairDoubleSecond (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181727,min (yhi c) (thi c),r c,thi c,
    secondDoubleYS c,secondDoubleS c,secondDoubleT c⟩
def pair72Cost (c:GridCell):ℕ:=(pair72 c).regularCountCap
def pair126Cost (c:GridCell):ℕ:=(pair126 c).regularCountCap
def doubleCost (c:GridCell):ℕ:=max (pairDoubleFirst c).regularCountCap
  (pairDoubleSecond c).regularCountCap
def RateFits (c:GridCell):Prop:=
  2382*LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c))≤bound*r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2382 (yhi c) (r c))≤bound
instance (c:GridCell):Decidable (RateFits c):=by unfold RateFits;infer_instance
def OrdinaryFits (c:GridCell):Prop:=ordinaryCost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (OrdinaryFits c):=by unfold OrdinaryFits;infer_instance
def Coprime72 (c:GridCell):Prop:=
  quotient72T c<tlo c ∨ quotient72YS c<ylo c ∨ quotient72S c<r c
instance (c:GridCell):Decidable (Coprime72 c):=by unfold Coprime72;infer_instance
def Coprime126 (c:GridCell):Prop:=
  quotient126T c<tlo c ∨ quotient126YS c<ylo c ∨ quotient126S c<r c
instance (c:GridCell):Decidable (Coprime126 c):=by unfold Coprime126;infer_instance
def PairGates (P:UnequalParameters):Prop:=
  1≤P.leftR ∧ P.leftY<prime ∧ P.leftR<prime ∧ P.leftZ<prime ∧
    P.mixedCost.y<prime ∧ P.mixedCost.r<prime ∧ P.mixedCost.z<prime
instance (P:UnequalParameters):Decidable (PairGates P):=by unfold PairGates;infer_instance
def Pair72Fits (c:GridCell):Prop:=
  length72 c≤52091 ∧ band72 c<sourceGap72 c ∧ Coprime72 c ∧
    PairGates (pair72 c) ∧ pair72Cost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Pair72Fits c):=by unfold Pair72Fits;infer_instance
def Pair126Fits (c:GridCell):Prop:=
  length126 c≤52091 ∧ band126 c<sourceGap126 c ∧ Coprime126 c ∧
    PairGates (pair126 c) ∧ pair126Cost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Pair126Fits c):=by unfold Pair126Fits;infer_instance
def Double126Fits (c:GridCell):Prop:=
  2340≤lengthDouble126 c ∧ lengthDouble126 c≤52091 ∧
    lengthDouble126 c<3*tlo c ∧
    bandDoubleFirst c+bandDoubleSecond c<sourceGapDouble126 c ∧
    PairGates (pairDoubleFirst c) ∧ PairGates (pairDoubleSecond c) ∧
    doubleCost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Double126Fits c):=by
  unfold Double126Fits;infer_instance
def Receipt (c:GridCell):Prop:=Valid c→RateFits c∨OrdinaryFits c∨Pair72Fits c∨
  Pair126Fits c∨Double126Fits c
instance (c:GridCell):Decidable (Receipt c):=by unfold Receipt;infer_instance

theorem receipt_coarse_0:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((0:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_1:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((1:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_2:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((2:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_3:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((3:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_4:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((4:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_5:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((5:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_6:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((6:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_7:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((7:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_8:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((8:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_9:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((9:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_10:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((10:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_11:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((11:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_12:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((12:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_13:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((13:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_14:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((14:Fin 16),(yi,ti))):=by decide
theorem receipt_coarse_15:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((15:Fin 16),(yi,ti))):=by decide
theorem receipt_fine:∀ c:FineCell,Receipt (Sum.inr (Sum.inl c)):=by decide
theorem receipt_unit:∀ c:UnitCell,Receipt (Sum.inr (Sum.inr c)):=by decide
theorem receipt (c:GridCell):Receipt c:=by
  rcases c with c|c
  · rcases c with ⟨ri,yi,ti⟩
    fin_cases ri
    · exact receipt_coarse_0 yi ti
    · exact receipt_coarse_1 yi ti
    · exact receipt_coarse_2 yi ti
    · exact receipt_coarse_3 yi ti
    · exact receipt_coarse_4 yi ti
    · exact receipt_coarse_5 yi ti
    · exact receipt_coarse_6 yi ti
    · exact receipt_coarse_7 yi ti
    · exact receipt_coarse_8 yi ti
    · exact receipt_coarse_9 yi ti
    · exact receipt_coarse_10 yi ti
    · exact receipt_coarse_11 yi ti
    · exact receipt_coarse_12 yi ti
    · exact receipt_coarse_13 yi ti
    · exact receipt_coarse_14 yi ti
    · exact receipt_coarse_15 yi ti
  · rcases c with c|c
    · exact receipt_fine c
    · exact receipt_unit c
def chosenCost (c:GridCell):ℕ:=
  if OrdinaryFits c then ordinaryCost c else if Pair72Fits c then pair72Cost c
  else if Pair126Fits c then pair126Cost c else doubleCost c
theorem chosenCost_with_rest (c:GridCell) (hv:Valid c) (hnr:¬RateFits c):
    chosenCost c+gridRestCost c≤bound:=by
  have hroutes:=(receipt c hv).resolve_left hnr
  by_cases ho:OrdinaryFits c
  · rw [chosenCost,if_pos ho]
    exact ho
  · have hpairs:=hroutes.resolve_left ho
    by_cases h72:Pair72Fits c
    · rw [chosenCost,if_neg ho,if_pos h72]
      exact h72.2.2.2.2
    · have hpairs':=hpairs.resolve_left h72
      by_cases h126:Pair126Fits c
      · rw [chosenCost,if_neg ho,if_neg h72,if_pos h126]
        exact h126.2.2.2.2
      · have hdouble:Double126Fits c:=(hpairs'.resolve_left h126)
        rw [chosenCost,if_neg ho,if_neg h72,if_neg h126]
        exact hdouble.2.2.2.2.2.2
end ProximityPrize.SubmissionLower.LocatorReplacementData
