/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836PureOffers
import ProximityPrize.SubmissionLower.Night6836OfferChecks
namespace Koala6836.PureOffers
open Koala6835.Offers (Offer)
set_option maxHeartbeats 400000
theorem raw_eq (r e z : Nat) : rowRaw r e z = ProximityPrize.SubmissionLower.Raw6836.rowRaw r e z := by rfl
private theorem chk_eq (r e hi cap n lo code:Nat) :
    check Offers.bank rowRaw r e hi cap n lo code =
    Koala6835.Offers.check Offers.bank ProximityPrize.SubmissionLower.Raw6836.rowRaw r e hi cap n lo code := by
  induction n generalizing lo code with
  | zero => rfl
  | succ n ih =>
    simp only [check,Koala6835.Offers.check]
    rw [ih]
    rfl
theorem row_eq (r e : Nat) : rowOK r e = Offers.rowOK r e := by
  simp only [rowOK,Offers.rowOK,singleOK,Offers.singleOK,binOK,Offers.binOK,chk_eq]
end Koala6836.PureOffers
