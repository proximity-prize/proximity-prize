import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

 













namespace ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research

open scoped BigOperators
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

 
def profileBNullity : Nat := 92637290

 


def derivativeFailureResidual (tCap yCap sCap j : Nat) : Nat :=
  ∑ u ∈ Finset.range (min tCap yCap + 1),
    ∑ rr ∈ Finset.range (min sCap u + 1),
      (tCap - u + 1) *
        (j * (agreements - (w - 1)) +
          (2 * agreements - w) * (u - rr) - (w - 1) * rr)

 



def iteratedDerivativeReplacementCost (j t y r : Nat) : Nat :=
  if j = 0 then
    ordinaryReplacementCost t y r
  else
    let rr := r - j
    let yy := y - j
    let tt := t - j
    let rp := max 2 rr
    let yp := max (rp + 1) yy
    let tp := max yp tt
    (if 1 ≤ rr then
        cellRegularCost tp yp rp
      else 0) +
      (cellTightProfile
        (profileA.weightedCap - j * (w - 1))
        tt (max rr 1)).countCap

def iteratedDerivativeTotalCost (j t y r : Nat) : Nat :=
  upstreamCellCost t y r + iteratedDerivativeReplacementCost j t y r

 

def HighTDerivativeRoute (t y r j : Nat) : Prop :=
  j ≤ r ∧
  (j = 0 ∨
    (0 < j ∧ derivativeFailureResidual
      (profileB.totalCap - t) (profileB.middleCap - y)
        (profileB.slopeCap - r) j < profileBNullity)) ∧
  iteratedDerivativeTotalCost j t y r ≤ 270096665443142692

instance highTDerivativeRouteDecidable (t y r j : Nat) :
    Decidable (HighTDerivativeRoute t y r j) := by
  unfold HighTDerivativeRoute
  infer_instance

 


def highTDerivativeOrder (t y r : Nat) : Nat :=
  (((List.range 14).map Nat.succ).find?
    (fun j ↦ decide (HighTDerivativeRoute t y r j))).getD 1

 



private theorem highTDerivativeOrder_certified_compressed :
    ∀ t : Fin 7, ∀ y : Fin 66, ∀ r : Fin 13,
      r.1 + 2 < y.1 →
      HighTDerivativeRoute (t.1 + 1660) y.1 (r.1 + 2)
          (highTDerivativeOrder (t.1 + 1660) y.1 (r.1 + 2)) ∧
        highTDerivativeOrder (t.1 + 1660) y.1 (r.1 + 2) < 15 := by
  unfold HighTDerivativeRoute highTDerivativeOrder
  decide

 


theorem highTDerivativeOrder_certified :
    ∀ t : Fin 1667, ∀ y : Fin 66, ∀ r : Fin 15,
      2 ≤ r.1 → r.1 < y.1 → y.1 ≤ t.1 → 1660 ≤ t.1 →
      HighTDerivativeRoute t.1 y.1 r.1
          (highTDerivativeOrder t.1 y.1 r.1) ∧
        highTDerivativeOrder t.1 y.1 r.1 < 15 := by
  intro t y r hr2 hry _ ht
  have htt : t.1 - 1660 < 7 := by omega
  have hrr : r.1 - 2 < 13 := by omega
  have htEq : t.1 - 1660 + 1660 = t.1 := Nat.sub_add_cancel ht
  have hrEq : r.1 - 2 + 2 = r.1 := Nat.sub_add_cancel hr2
  have h := highTDerivativeOrder_certified_compressed
    ⟨t.1 - 1660, htt⟩ y ⟨r.1 - 2, hrr⟩ (by simpa only [hrEq] using hry)
  simpa only [htEq, hrEq] using h

 


theorem highTDerivativeRoute_exists :
    ∀ t : Fin 1667, ∀ y : Fin 66, ∀ r : Fin 15,
      2 ≤ r.1 → r.1 < y.1 → y.1 ≤ t.1 → 1660 ≤ t.1 →
      ∃ j : Fin 15, HighTDerivativeRoute t.1 y.1 r.1 j.1 := by
  intro t y r hr2 hry hyt ht
  have h := highTDerivativeOrder_certified t y r hr2 hry hyt ht
  exact ⟨⟨highTDerivativeOrder t.1 y.1 r.1, h.2⟩, h.1⟩

theorem highTRouterCap_lt_mcaBudget :
    270096665443142692 < ContactMovingSeedless6750Research.mcaBudget := by
  decide

end ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research

#print axioms ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research.highTDerivativeRoute_exists
#print axioms ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research.highTRouterCap_lt_mcaBudget
