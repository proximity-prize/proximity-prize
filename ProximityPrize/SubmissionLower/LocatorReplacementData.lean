import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorChannelUpper6765
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open RCN100 RCN260 LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorChannelUpper6765 LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private abbrev prime:ℕ:=2130706433
private abbrev bound:ℕ:=271800583557655343
private abbrev delta:ℕ:=50637
private abbrev sourceSlopeBase:ℕ:=96042618
private abbrev sourceDebtBase:ℕ:=256447286151
private abbrev sourceY:ℕ:=128
private abbrev sourceS:ℕ:=27
private abbrev sourceSlopeBase126:ℕ:=362777280
private abbrev sourceDebtBase126:ℕ:=883856918630
private abbrev sourceY126:ℕ:=174
private abbrev sourceS126:ℕ:=39
private abbrev sourceMaxL:ℕ:=52091

def quotientY (c:Cell):ℕ:=sourceY-y c
def quotientS (c:Cell):ℕ:=sourceS-r c
def cofactorY (c:Cell):ℕ:=sourceY-y c-y c
def cofactorS (c:Cell):ℕ:=sourceS-r c-r c
def sourceSlots (c:Cell):ℕ:=
  slotCount (quotientY c) (quotientS c)+
    slotCount (cofactorY c) (cofactorS c)
def sourceSlope (c:Cell):ℕ:=sourceSlopeBase-delta*sourceSlots c
def sourceDebt (c:Cell):ℕ:=
  sourceDebtBase-delta*sourceSlots c*(tlo c-1)
def rawLength (c:Cell):ℕ:=
  max (2*tlo c) (sourceDebt c/sourceSlope c+1)
def sourceLength (c:Cell):ℕ:=
  if cofactorY c<y c ∨ cofactorS c<r c then rawLength c
  else min (rawLength c) (3*tlo c-1)
def quotientT (c:Cell):ℕ:=sourceLength c-tlo c
def cofactorT (c:Cell):ℕ:=sourceLength c-tlo c-tlo c
def sourceNullity (c:Cell):ℕ:=
  sourceSlopeBase*sourceLength c-sourceDebtBase

def quotientPair (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    quotientY c,quotientS c,quotientT c⟩
def cofactorPair (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    cofactorY c,cofactorS c,cofactorT c⟩
def sourceCost (c:Cell):ℕ:=
  max (quotientPair c).regularCountCap (cofactorPair c).regularCountCap

def quotientY126 (c:Cell):ℕ:=sourceY126-y c
def quotientS126 (c:Cell):ℕ:=sourceS126-r c
def cofactorY126 (c:Cell):ℕ:=sourceY126-y c-y c
def cofactorS126 (c:Cell):ℕ:=sourceS126-r c-r c
def sourceSlots126 (c:Cell):ℕ:=
  slotCount (quotientY126 c) (quotientS126 c)+
    slotCount (cofactorY126 c) (cofactorS126 c)
def sourceSlope126 (c:Cell):ℕ:=sourceSlopeBase126-delta*sourceSlots126 c
def sourceDebt126 (c:Cell):ℕ:=
  sourceDebtBase126-delta*sourceSlots126 c*(tlo c-1)
def rawLength126 (c:Cell):ℕ:=
  max (2*tlo c) (sourceDebt126 c/sourceSlope126 c+1)
def sourceLength126 (c:Cell):ℕ:=
  if cofactorY126 c<y c ∨ cofactorS126 c<r c then rawLength126 c
  else min (rawLength126 c) (3*tlo c-1)
def quotientT126 (c:Cell):ℕ:=sourceLength126 c-tlo c
def cofactorT126 (c:Cell):ℕ:=sourceLength126 c-tlo c-tlo c
def sourceNullity126 (c:Cell):ℕ:=
  sourceSlopeBase126*sourceLength126 c-sourceDebtBase126
def quotientPair126 (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    quotientY126 c,quotientS126 c,quotientT126 c⟩
def cofactorPair126 (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    cofactorY126 c,cofactorS126 c,cofactorT126 c⟩
def sourceCost126 (c:Cell):ℕ:=
  max (quotientPair126 c).regularCountCap (cofactorPair126 c).regularCountCap

def hybridLength (c:Cell):ℕ:=4*tlo c+30000
def hybridFirstT (c:Cell):ℕ:=hybridLength c-tlo c
def hybridFirstY (c:Cell):ℕ:=min (sourceY126-y c) (hybridFirstT c)
def hybridFirstS (c:Cell):ℕ:=min (sourceS126-r c) (hybridFirstY c)
def hybridSecondT (c:Cell):ℕ:=hybridLength c-2*tlo c
def hybridSecondY (c:Cell):ℕ:=min (sourceY126-2*y c) (hybridSecondT c)
def hybridSecondS (c:Cell):ℕ:=min (sourceS126-2*r c) (hybridSecondY c)
def hybridThirdT (c:Cell):ℕ:=hybridLength c-3*tlo c
def hybridThirdY (c:Cell):ℕ:=min (sourceY126-3*y c) (hybridThirdT c)
def hybridThirdS (c:Cell):ℕ:=min (sourceS126-3*r c) (hybridThirdY c)
def hybridFourthT (c:Cell):ℕ:=hybridLength c-4*tlo c
def hybridFourthY (c:Cell):ℕ:=min (sourceY126-4*y c) (hybridFourthT c)
def hybridFourthS (c:Cell):ℕ:=min (sourceS126-4*r c) (hybridFourthY c)
def hybridNullity (c:Cell):ℕ:=
  sourceSlopeBase126*hybridLength c-sourceDebtBase126
def hybridPairFirst (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    hybridFirstY c,hybridFirstS c,hybridFirstT c⟩
def hybridPairSecond (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    hybridSecondY c,hybridSecondS c,hybridSecondT c⟩
def hybridPairThird (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    hybridThirdY c,hybridThirdS c,hybridThirdT c⟩
def hybridPairFourth (c:Cell):UnequalParameters:=
  ⟨262144,131071,181707,y c,r c,thi c,
    hybridFourthY c,hybridFourthS c,hybridFourthT c⟩
def hybridCost (c:Cell):ℕ:=max (hybridPairFirst c).regularCountCap
  (max (hybridPairSecond c).regularCountCap
    (max (hybridPairThird c).regularCountCap (hybridPairFourth c).regularCountCap))

def exactRest (c:Cell):ℕ:=
  remainingCost 2556 78 17 131072 131073 (cap (tlo c) (y c) (r c))
def noBadFits (c:Cell):Prop:=
  2556*paddedCost 131072 131073 (cap (thi c) (y c) (r c))≤
    bound*tlo c
def ordinaryFits (c:Cell):Prop:=
  paddedCost 131072 131073 (cap (thi c) (y c) (r c))+exactRest c≤bound
def PairGates (P:UnequalParameters):Prop:=
  1≤P.leftR ∧ P.leftY<prime ∧ P.leftR<prime ∧ P.leftZ<prime ∧
    P.mixedCost.y<prime ∧ P.mixedCost.r<prime ∧ P.mixedCost.z<prime
def sourceFits (c:Cell):Prop:=
  2671≤sourceLength c ∧ sourceLength c≤sourceMaxL ∧
    2*tlo c≤sourceLength c ∧
    delta*channelUpper (quotientT c) (quotientY c) (quotientS c)+
      delta*channelUpper (cofactorT c) (cofactorY c) (cofactorS c)<
        sourceNullity c ∧
    delta*channelUpper (quotientT c) (quotientY c) (quotientS c)+
      (cofactorT c+1)*delta<
        sourceNullity c ∧
    (cofactorT c<tlo c ∨ cofactorY c<y c ∨ cofactorS c<r c) ∧
    PairGates (quotientPair c) ∧ PairGates (cofactorPair c) ∧
    sourceCost c+exactRest c≤bound
def sourceFits126 (c:Cell):Prop:=
  2600≤sourceLength126 c ∧ sourceLength126 c≤sourceMaxL ∧
    2*tlo c≤sourceLength126 c ∧
    delta*channelUpper (quotientT126 c) (quotientY126 c) (quotientS126 c)+
      delta*channelUpper (cofactorT126 c) (cofactorY126 c) (cofactorS126 c)<
        sourceNullity126 c ∧
    delta*channelUpper (quotientT126 c) (quotientY126 c) (quotientS126 c)+
      (cofactorT126 c+1)*delta<sourceNullity126 c ∧
    (cofactorT126 c<tlo c ∨ cofactorY126 c<y c ∨ cofactorS126 c<r c) ∧
    PairGates (quotientPair126 c) ∧ PairGates (cofactorPair126 c) ∧
    sourceCost126 c+exactRest c≤bound
def hybridFits (c:Cell):Prop:=
  2600≤hybridLength c ∧ hybridLength c≤sourceMaxL ∧
    delta*channelCount (hybridFirstT c) (hybridFirstY c) (hybridFirstS c)+
    delta*channelCount (hybridSecondT c) (hybridSecondY c) (hybridSecondS c)+
      delta*channelCount (hybridThirdT c) (hybridThirdY c) (hybridThirdS c)+
      delta*channelCount (hybridFourthT c) (hybridFourthY c) (hybridFourthS c)<
        hybridNullity c ∧
    (hybridFourthT c<tlo c ∨ hybridFourthY c<y c ∨ hybridFourthS c<r c) ∧
    PairGates (hybridPairFirst c) ∧ PairGates (hybridPairSecond c) ∧
    PairGates (hybridPairThird c) ∧ PairGates (hybridPairFourth c) ∧
    hybridCost c+exactRest c≤bound

instance (c:Cell):Decidable (noBadFits c):=by unfold noBadFits;infer_instance
instance (c:Cell):Decidable (ordinaryFits c):=by unfold ordinaryFits;infer_instance
instance (P:UnequalParameters):Decidable (PairGates P):=by unfold PairGates;infer_instance
instance (c:Cell):Decidable (sourceFits c):=by unfold sourceFits;infer_instance
instance (c:Cell):Decidable (sourceFits126 c):=by unfold sourceFits126;infer_instance
instance (c:Cell):Decidable (hybridFits c):=by unfold hybridFits;infer_instance

def Receipt (c:Cell):Prop:=
  Valid c→noBadFits c∨ordinaryFits c∨sourceFits c∨sourceFits126 c∨hybridFits c
instance (c:Cell):Decidable (Receipt c):=by unfold Receipt;infer_instance

def chosenCost (c:Cell):ℕ:=
  if ordinaryFits c then
    paddedCost 131072 131073 (cap (thi c) (y c) (r c))
  else if sourceFits c then sourceCost c
  else if sourceFits126 c then sourceCost126 c else hybridCost c

end ProximityPrize.SubmissionLower.LocatorReplacementData
