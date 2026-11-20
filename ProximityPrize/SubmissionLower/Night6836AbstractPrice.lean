/- Apache-2.0. Connect an arbitrary physically proved window catalogue to the
   68.36 singleton budget and the multifactor discretization on the same fibre. -/
import ProximityPrize.SubmissionLower.Night6836ActualCost
import ProximityPrize.SubmissionLower.Night6836OfferAll

namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical
open RCN095 RCN266 Koala6831Moving Koala6831MovingPaid LocatorFactorAggregate
open Koala6835.Offers (valid)
open Koala6836.Offers (bank)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

theorem factor_bounds_of_bank {x:I ↪ K} {H:MvPolynomial (Fin 4) K} {S:Finset K}
    {sel:K→Polynomial K} {u v:I→K} {D:ℕ} (A:Original x H S sel u v D)
    (F:RegularIndex H) {r e z:ℕ} (pos:0<r) (eq:contactFlag F.1=⟨z,e,r⟩)
    (cap:r≤18 ∧ r+e≤76 ∧ r+e+z≤9352) (W:ℕ→P33.Window)
    (good:∀i,P33.WindowCount (W i)) (shape:∀i,admissible (W i))
    (realization:∀i,valid (bank i) r e (r+e+z) (r+e+z) →
      offer_of_window (W i)=bank i) :
    (regularFiber H S sel F).card≤Koala6836.Tables.oneUnits r e (z/100)*10000000000000 ∧
    (r+e+z≤Koala6836.Room.maxTotal r e →
      (regularFiber H S sel F).card≤Koala6836.Room.budget r e (r+e+z)) := by
  have hc := actual_cost A F eq cap W good shape
  have priced (i : ℕ) (h : valid (bank i) r e (r+e+z) (r+e+z)) :
      (regularFiber H S sel F).card≤(bank i).fee := by
    have hw := realization i h
    have hv := hc.2 i (hw.symm ▸ h)
    exact hw ▸ hv
  have lb : r+e ≤ r+e+z := Nat.le_add_right _ _
  constructor
  · simpa using Koala6836.Offers.one_price pos cap.1 cap.2.1 lb cap.2.2 hc.1 priced
  · intro ht
    exact Koala6836.Offers.singleton_price pos cap.1 cap.2.1 lb ht hc.1 priced

#print axioms factor_bounds_of_bank
end ProximityPrize.SubmissionLower.Raw6836
