import ProximityPrize.SubmissionLower.LocatorReplacementGrid
import ProximityPrize.SubmissionLower.LocatorRateCover
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open scoped BigOperators
open LocatorReplacementGrid RCN100 RCN260 RCN302 RCN180
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
private abbrev prime:ℕ:=2130706433
abbrev bound:ℕ:=271797226259522258
private abbrev delta:ℕ:=50666
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

def length72 (c:GridCell):ℕ:=suggestedLength 28489197 92785577302 3106 99 21 c
def length126 (c:GridCell):ℕ:=suggestedLength 421185415 973937604520 2255 178 40 c
def quotient72D (c:GridCell):ℕ:=13084992-(131071*ylo c-r c)-delta
def quotient72T (c:GridCell):ℕ:=length72 c-tlo c
def quotient72YS (c:GridCell):ℕ:=99-ylo c
def quotient72S (c:GridCell):ℕ:=21-r c
def quotient126D (c:GridCell):ℕ:=23443944-(131071*ylo c-r c)-delta
def quotient126T (c:GridCell):ℕ:=length126 c-tlo c
def quotient126YS (c:GridCell):ℕ:=178-ylo c
def quotient126S (c:GridCell):ℕ:=40-r c
def band72 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient72T c) (quotient72YS c) (quotient72S c)
def band126 (c:GridCell):ℕ:=delta*LocatorLowQuotient.channelCount
  (quotient126T c) (quotient126YS c) (quotient126S c)
def sourceGap72 (c:GridCell):ℕ:=
  28489197*length72 c-92785577302
def sourceGap126 (c:GridCell):ℕ:=
  421185415*length126 c-973937604520
def pair72 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181736,min (yhi c) (thi c),r c,thi c,
    quotient72YS c,quotient72S c,quotient72T c⟩
def pair126 (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181736,min (yhi c) (thi c),r c,thi c,
    quotient126YS c,quotient126S c,quotient126T c⟩
def pair72Cost (c:GridCell):ℕ:=(pair72 c).regularCountCap
def pair126Cost (c:GridCell):ℕ:=(pair126 c).regularCountCap
def staircaseLength:ℕ:=3057
def staircaseQD (c:GridCell):ℕ:=
  23443944-delta-(131071*ylo c-r c)
def staircaseQT (c:GridCell):ℕ:=staircaseLength-tlo c
def staircaseQYS (c:GridCell):ℕ:=178-ylo c
def staircaseQS (c:GridCell):ℕ:=40-r c
def staircaseRD (c:GridCell):ℕ:=
  23443944-delta-delta-2*(131071*ylo c-r c)
def staircaseRT (c:GridCell):ℕ:=staircaseLength-2*tlo c
def staircaseRYS (c:GridCell):ℕ:=178-2*ylo c
def staircaseRS (c:GridCell):ℕ:=40-2*r c
def staircaseCube (c:GridCell):ℕ:=coefficientCount
  (23443944-delta-delta-3*(131071*ylo c-r c)) 131071
  (staircaseLength-3*tlo c) (40-3*r c)
def staircaseBand (c:GridCell):ℕ:=delta*(
  LocatorLowQuotient.channelCount (staircaseQT c) (staircaseQYS c) (staircaseQS c)+
  LocatorLowQuotient.channelCount (staircaseRT c) (staircaseRYS c) (staircaseRS c))
def staircaseSourceGap:ℕ:=313626209135
def staircasePairQ (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181736,min (yhi c) (thi c),r c,thi c,
    staircaseQYS c,staircaseQS c,staircaseQT c⟩
def staircasePairR (c:GridCell):UnequalParameters:=
  ⟨262144,131071,181736,min (yhi c) (thi c),r c,thi c,
    staircaseRYS c,staircaseRS c,staircaseRT c⟩
def staircaseCost (c:GridCell):ℕ:=
  max (staircasePairQ c).regularCountCap (staircasePairR c).regularCountCap
def RateFits (c:GridCell):Prop:=
  2319*LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c))≤bound*r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2319 (yhi c) (r c))≤bound
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
  length72 c≤55600 ∧ band72 c<sourceGap72 c ∧ Coprime72 c ∧
    PairGates (pair72 c) ∧ pair72Cost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Pair72Fits c):=by unfold Pair72Fits;infer_instance
def Pair126Fits (c:GridCell):Prop:=
  length126 c≤55600 ∧ band126 c<sourceGap126 c ∧ Coprime126 c ∧
    PairGates (pair126 c) ∧ pair126Cost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (Pair126Fits c):=by unfold Pair126Fits;infer_instance
def StaircaseFits (c:GridCell):Prop:=
  staircaseBand c+staircaseCube c<staircaseSourceGap ∧
    PairGates (staircasePairQ c) ∧ PairGates (staircasePairR c) ∧
    staircaseCost c+gridRestCost c≤bound
instance (c:GridCell):Decidable (StaircaseFits c):=by
  unfold StaircaseFits;infer_instance
def Receipt (c:GridCell):Prop:=Valid c→RateFits c∨OrdinaryFits c∨Pair72Fits c∨
  Pair126Fits c∨StaircaseFits c
instance (c:GridCell):Decidable (Receipt c):=by unfold Receipt;infer_instance

end ProximityPrize.SubmissionLower.LocatorReplacementData
