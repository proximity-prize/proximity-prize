import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorChannelUpper6765
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open RCN100 RCN260 LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorChannelUpper6765
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private abbrev prime:ℕ:=2130706433
private abbrev bound:ℕ:=271696008548359000
private abbrev delta:ℕ:=50647
private abbrev sourceSlopeBase:ℕ:=99050238
private abbrev sourceDebtBase:ℕ:=256656218091
private abbrev sourceY:ℕ:=128
private abbrev sourceS:ℕ:=27
private abbrev sourceSlopeBase126:ℕ:=370614480
private abbrev sourceDebtBase126:ℕ:=884603972630
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
  ⟨262144,131071,181717,y c,r c,thi c,
    quotientY c,quotientS c,quotientT c⟩
def cofactorPair (c:Cell):UnequalParameters:=
  ⟨262144,131071,181717,y c,r c,thi c,
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
  ⟨262144,131071,181717,y c,r c,thi c,
    quotientY126 c,quotientS126 c,quotientT126 c⟩
def cofactorPair126 (c:Cell):UnequalParameters:=
  ⟨262144,131071,181717,y c,r c,thi c,
    cofactorY126 c,cofactorS126 c,cofactorT126 c⟩
def sourceCost126 (c:Cell):ℕ:=
  max (quotientPair126 c).regularCountCap (cofactorPair126 c).regularCountCap

def exactRest (c:Cell):ℕ:=
  remainingCost 2450 77 17 131072 131073 (cap (tlo c) (y c) (r c))
def noBadFits (c:Cell):Prop:=
  2450*paddedCost 131072 131073 (cap (thi c) (y c) (r c))≤
    bound*tlo c
def ordinaryFits (c:Cell):Prop:=
  paddedCost 131072 131073 (cap (thi c) (y c) (r c))+exactRest c≤bound
def PairGates (P:UnequalParameters):Prop:=
  1≤P.leftR ∧ P.leftY<prime ∧ P.leftR<prime ∧ P.leftZ<prime ∧
    P.mixedCost.y<prime ∧ P.mixedCost.r<prime ∧ P.mixedCost.z<prime
def sourceFits (c:Cell):Prop:=
  2600≤sourceLength c ∧ sourceLength c≤sourceMaxL ∧
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

instance (c:Cell):Decidable (noBadFits c):=by unfold noBadFits;infer_instance
instance (c:Cell):Decidable (ordinaryFits c):=by unfold ordinaryFits;infer_instance
instance (P:UnequalParameters):Decidable (PairGates P):=by unfold PairGates;infer_instance
instance (c:Cell):Decidable (sourceFits c):=by unfold sourceFits;infer_instance
instance (c:Cell):Decidable (sourceFits126 c):=by unfold sourceFits126;infer_instance

def Receipt (c:Cell):Prop:=
  Valid c→noBadFits c∨ordinaryFits c∨sourceFits c∨sourceFits126 c
instance (c:Cell):Decidable (Receipt c):=by unfold Receipt;infer_instance

def chosenCost (c:Cell):ℕ:=
  if ordinaryFits c then
    paddedCost 131072 131073 (cap (thi c) (y c) (r c))
  else if sourceFits c then sourceCost c else sourceCost126 c

end ProximityPrize.SubmissionLower.LocatorReplacementData
