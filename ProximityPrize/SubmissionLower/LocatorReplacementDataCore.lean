import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorRateCover
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open scoped BigOperators
open LocatorReplacementGrid RCN260 RCN302 RCN180
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
abbrev prime:ℕ:=2130706433
abbrev bound:ℕ:=271673448487290497
abbrev delta:ℕ:=50647
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

def length72 (c:GridCell):ℕ:=suggestedLength 25795605 92641402414 3592 99 21 c
def length126 (c:GridCell):ℕ:=suggestedLength 370614480 884603972630 2387 174 39 c
def lengthDouble126 (c:GridCell):ℕ:=2*tlo c+1000
def lengthTriple126 (c:GridCell):ℕ:=3*tlo c+500
def quotient72D (c:GridCell):ℕ:=13083624-(131071*ylo c-r c)-delta
def quotient72T (c:GridCell):ℕ:=length72 c-tlo c
def quotient72YS (c:GridCell):ℕ:=99-ylo c
def quotient72S (c:GridCell):ℕ:=21-r c
def quotient126D (c:GridCell):ℕ:=22896342-(131071*ylo c-r c)-delta
def quotient126T (c:GridCell):ℕ:=length126 c-tlo c
def quotient126YS (c:GridCell):ℕ:=174-ylo c
def quotient126S (c:GridCell):ℕ:=39-r c
def quotientDoubleT (c:GridCell):ℕ:=lengthDouble126 c-tlo c
def quotientDoubleYS (c:GridCell):ℕ:=174-ylo c
def quotientDoubleS (c:GridCell):ℕ:=39-r c
def secondDoubleT (c:GridCell):ℕ:=lengthDouble126 c-2*tlo c
def secondDoubleYS (c:GridCell):ℕ:=174-2*ylo c
def secondDoubleS (c:GridCell):ℕ:=39-2*r c
def firstTripleT (c:GridCell):ℕ:=lengthTriple126 c-tlo c
def firstTripleYS (c:GridCell):ℕ:=min (174-ylo c) (firstTripleT c)
def firstTripleS (c:GridCell):ℕ:=min (39-r c) (firstTripleYS c)
def secondTripleT (c:GridCell):ℕ:=lengthTriple126 c-2*tlo c
def secondTripleYS (c:GridCell):ℕ:=min (174-2*ylo c) (secondTripleT c)
def secondTripleS (c:GridCell):ℕ:=min (39-2*r c) (secondTripleYS c)
def thirdTripleT (c:GridCell):ℕ:=lengthTriple126 c-3*tlo c
def thirdTripleYS (c:GridCell):ℕ:=min (174-3*ylo c) (thirdTripleT c)
def thirdTripleS (c:GridCell):ℕ:=min (39-3*r c) (thirdTripleYS c)
def band72 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient72T c) (quotient72YS c) (quotient72S c)
def band126 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient126T c) (quotient126YS c) (quotient126S c)
def bandDoubleFirst (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotientDoubleT c) (quotientDoubleYS c) (quotientDoubleS c)
def bandDoubleSecond (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (secondDoubleT c) (secondDoubleYS c) (secondDoubleS c)
def bandTripleFirst (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (firstTripleT c) (firstTripleYS c) (firstTripleS c)
def bandTripleSecond (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (secondTripleT c) (secondTripleYS c) (secondTripleS c)
def bandTripleThird (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (thirdTripleT c) (thirdTripleYS c) (thirdTripleS c)
def sourceGap72 (c:GridCell):ℕ:=
  25795605*length72 c-92641402414
def sourceGap126 (c:GridCell):ℕ:=
  370614480*length126 c-884603972630
def sourceGapDouble126 (c:GridCell):ℕ:=
  370614480*lengthDouble126 c-884603972630
def sourceGapTriple126 (c:GridCell):ℕ:=
  370614480*lengthTriple126 c-884603972630
def pair72 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    quotient72YS c,quotient72S c,quotient72T c⟩
def pair126 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    quotient126YS c,quotient126S c,quotient126T c⟩
def pairDoubleFirst (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    quotientDoubleYS c,quotientDoubleS c,quotientDoubleT c⟩
def pairDoubleSecond (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    secondDoubleYS c,secondDoubleS c,secondDoubleT c⟩
def pairTripleFirst (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    firstTripleYS c,firstTripleS c,firstTripleT c⟩
def pairTripleSecond (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    secondTripleYS c,secondTripleS c,secondTripleT c⟩
def pairTripleThird (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181717,min (yhi c) (thi c),r c,thi c,
    thirdTripleYS c,thirdTripleS c,thirdTripleT c⟩
def pair72Cost (c:GridCell):ℕ:=(pair72 c).regularCountCap
def pair126Cost (c:GridCell):ℕ:=(pair126 c).regularCountCap
def doubleCost (c:GridCell):ℕ:=max (pairDoubleFirst c).regularCountCap
  (pairDoubleSecond c).regularCountCap
def tripleCost (c:GridCell):ℕ:=max (pairTripleFirst c).regularCountCap
  (max (pairTripleSecond c).regularCountCap (pairTripleThird c).regularCountCap)
def RateFits (c:GridCell):Prop:=
  2445*LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c))≤bound*r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2445 (yhi c) (r c))≤bound
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
  2387≤lengthDouble126 c ∧ lengthDouble126 c≤52091 ∧
    lengthDouble126 c<3*tlo c ∧
    bandDoubleFirst c+bandDoubleSecond c<sourceGapDouble126 c ∧
    PairGates (pairDoubleFirst c) ∧ PairGates (pairDoubleSecond c) ∧
    doubleCost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Double126Fits c):=by
  unfold Double126Fits;infer_instance
def CoprimeTriple126 (c:GridCell):Prop:=
  thirdTripleT c<tlo c ∨ thirdTripleYS c<ylo c ∨ thirdTripleS c<r c
instance (c:GridCell):Decidable (CoprimeTriple126 c):=by
  unfold CoprimeTriple126;infer_instance
def Triple126Fits (c:GridCell):Prop:=
  2387≤lengthTriple126 c ∧ lengthTriple126 c≤52091 ∧
    bandTripleFirst c+bandTripleSecond c+bandTripleThird c<sourceGapTriple126 c ∧
    CoprimeTriple126 c ∧ PairGates (pairTripleFirst c) ∧
    PairGates (pairTripleSecond c) ∧ PairGates (pairTripleThird c) ∧
    tripleCost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Triple126Fits c):=by
  unfold Triple126Fits;infer_instance
def Receipt (c:GridCell):Prop:=Valid c→RateFits c∨OrdinaryFits c∨Pair72Fits c∨
  Pair126Fits c∨Double126Fits c∨Triple126Fits c
instance (c:GridCell):Decidable (Receipt c):=by unfold Receipt;infer_instance
end ProximityPrize.SubmissionLower.LocatorReplacementData
