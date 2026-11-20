/- Apache-2.0. 68.36 degree-interval receipts by Bome2017 over the BitWonka and Lucieno physical bounds. -/
import ProximityPrize.SubmissionLower.Night6836OfferData
namespace Koala6836.Offers
open Koala6835.Offers (Offer valid)
def same (x y:Offer) : Bool := decide (x.r=y.r ∧ x.y=y.y ∧ x.hi=y.hi ∧ x.lo=y.lo ∧ x.fee=y.fee)
theorem eq_of_same {x y:Offer} (h:same x y = true) : x = y := by
  cases x with
  | mk r y1 t l f =>
    cases y with
    | mk r2 y2 t2 l2 f2 =>
      rcases of_decide_eq_true h with ⟨rfl,rfl,rfl,rfl,rfl⟩
      rfl
theorem bank_index (i r e t:Nat) (hr:0<r) (h:valid (bank i) r e t t) : i<603 := by
  by_cases hi : i<603
  · exact hi
  · have hs : 603= catalogue.size := by decide +kernel
    have hbound : catalogue.size ≤ i := hs ▸ Nat.le_of_not_lt hi
    have hnone : catalogue[i]? = none := Array.getElem?_eq_none hbound
    have he : bank i = ⟨0,0,0,1,0⟩ := by simp only [bank,Array.getD_eq_getD_getElem?,hnone,Option.getD_none]
    have rr := h.1
    rw [he] at rr
    change r ≤ 0 at rr
    exact False.elim (Nat.not_le_of_gt hr rr)
end Koala6836.Offers
