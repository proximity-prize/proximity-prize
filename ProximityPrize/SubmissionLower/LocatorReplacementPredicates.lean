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
abbrev bound:ℕ:=267000000000000000
def quotient95D (c:Cell):ℕ:=17268720 - (131071*ylo c - r c) - 50706
def quotient95T (c:Cell):ℕ:=2869 - tlo c
def quotient95YS (c:Cell):ℕ:=131 - ylo c
def quotient95S (c:Cell):ℕ:=29 - r c
def band95 (c:Cell):ℕ :=
  50706*LocatorLowQuotient.channelCount
    (quotient95T c) (quotient95YS c) (quotient95S c)
def quotient72D (c:Cell):ℕ:=13087872 - (131071*ylo c - r c) - 50706
def quotient72T (c:Cell):ℕ:=8526 - tlo c
def quotient72YS (c:Cell):ℕ:=99 - ylo c
def quotient72S (c:Cell):ℕ:=21 - r c
def band72 (c:Cell):ℕ :=
  50706*LocatorLowQuotient.channelCount
    (quotient72T c) (quotient72YS c) (quotient72S c)
def pair95 (c:Cell):UnequalParameters :=
  ⟨262144,131071,181776,min (yhi c) (thi c),r c,thi c,
    quotient95YS c,quotient95S c,quotient95T c⟩
def pair72 (c:Cell):UnequalParameters :=
  ⟨262144,131071,181776,min (yhi c) (thi c),r c,thi c,
    quotient72YS c,quotient72S c,quotient72T c⟩
def pair95Cost (c:Cell):ℕ:=(pair95 c).regularCountCap
def pair72Cost (c:Cell):ℕ:=(pair72 c).regularCountCap
def RateFits (c:Cell):Prop :=
  2080*LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap (r c) (r c) (r c))≤bound*r c ∧
    LocatorFactorAggregate.paddedCost 131072 131073
      (LocatorFactorAggregate.cap 2080 (yhi c) (r c))≤bound
instance (c:Cell):Decidable (RateFits c):=by
  unfold RateFits
  infer_instance
def OrdinaryFits (c:Cell):Prop:=ordinaryCost c+gridRestCost c≤bound
instance (c:Cell):Decidable (OrdinaryFits c):=by
  unfold OrdinaryFits
  infer_instance
def Coprime95 (c:Cell):Prop :=
  quotient95T c<tlo c ∨ quotient95YS c<ylo c ∨ quotient95S c<r c
instance (c:Cell):Decidable (Coprime95 c):=by
  unfold Coprime95
  infer_instance
def Coprime72 (c:Cell):Prop :=
  quotient72T c<tlo c ∨ quotient72YS c<ylo c ∨ quotient72S c<r c
instance (c:Cell):Decidable (Coprime72 c):=by
  unfold Coprime72
  infer_instance
def PairGates (P:UnequalParameters):Prop :=
  1≤P.leftR ∧ P.leftY<prime ∧ P.leftR<prime ∧ P.leftZ<prime ∧
    P.mixedCost.y<prime ∧ P.mixedCost.r<prime ∧ P.mixedCost.z<prime
instance (P:UnequalParameters):Decidable (PairGates P):=by
  unfold PairGates
  infer_instance
def Pair95Fits (c:Cell):Prop :=
  band95 c<105035624165 ∧ Coprime95 c ∧ PairGates (pair95 c) ∧
    pair95Cost c+gridRestCost c≤bound
instance (c:Cell):Decidable (Pair95Fits c):=by
  unfold Pair95Fits
  infer_instance
def Pair72Fits (c:Cell):Prop :=
  band72 c<198158348960 ∧ Coprime72 c ∧ PairGates (pair72 c) ∧
    pair72Cost c+gridRestCost c≤bound
instance (c:Cell):Decidable (Pair72Fits c):=by
  unfold Pair72Fits
  infer_instance
def Receipt (c:Cell):Prop:=Valid c →
  RateFits c ∨ OrdinaryFits c ∨ Pair95Fits c ∨ Pair72Fits c
instance (c:Cell):Decidable (Receipt c):=by
  unfold Receipt
  infer_instance
end ProximityPrize.SubmissionLower.LocatorReplacementData
