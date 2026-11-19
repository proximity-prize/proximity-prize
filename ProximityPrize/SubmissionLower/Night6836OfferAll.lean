/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836PureBridge
import ProximityPrize.SubmissionLower.Night6836PureR01
import ProximityPrize.SubmissionLower.Night6836PureR02
import ProximityPrize.SubmissionLower.Night6836PureR03
import ProximityPrize.SubmissionLower.Night6836PureR04
import ProximityPrize.SubmissionLower.Night6836PureR05
import ProximityPrize.SubmissionLower.Night6836PureR06
import ProximityPrize.SubmissionLower.Night6836PureR07
import ProximityPrize.SubmissionLower.Night6836PureR08
import ProximityPrize.SubmissionLower.Night6836PureR09
import ProximityPrize.SubmissionLower.Night6836PureR10
import ProximityPrize.SubmissionLower.Night6836PureR11
import ProximityPrize.SubmissionLower.Night6836PureR12
import ProximityPrize.SubmissionLower.Night6836PureR13
import ProximityPrize.SubmissionLower.Night6836PureR14
import ProximityPrize.SubmissionLower.Night6836PureR15
import ProximityPrize.SubmissionLower.Night6836PureR16
import ProximityPrize.SubmissionLower.Night6836PureR17
import ProximityPrize.SubmissionLower.Night6836PureR18
namespace Koala6836.Offers
open Koala6835.Offers (valid)
open ProximityPrize.SubmissionLower.Raw6836
open Koala6836.Tables Koala6836.Room
theorem all_rows (r e : ℕ) (hr : 1≤r) (hR : r≤18) (hY : r+e≤76) : rowOK r e = true := by
  interval_cases r
  · exact (PureOffers.row_eq 1 e ▸ PureOffers.ok1 e (by omega))
  · exact (PureOffers.row_eq 2 e ▸ PureOffers.ok2 e (by omega))
  · exact (PureOffers.row_eq 3 e ▸ PureOffers.ok3 e (by omega))
  · exact (PureOffers.row_eq 4 e ▸ PureOffers.ok4 e (by omega))
  · exact (PureOffers.row_eq 5 e ▸ PureOffers.ok5 e (by omega))
  · exact (PureOffers.row_eq 6 e ▸ PureOffers.ok6 e (by omega))
  · exact (PureOffers.row_eq 7 e ▸ PureOffers.ok7 e (by omega))
  · exact (PureOffers.row_eq 8 e ▸ PureOffers.ok8 e (by omega))
  · exact (PureOffers.row_eq 9 e ▸ PureOffers.ok9 e (by omega))
  · exact (PureOffers.row_eq 10 e ▸ PureOffers.ok10 e (by omega))
  · exact (PureOffers.row_eq 11 e ▸ PureOffers.ok11 e (by omega))
  · exact (PureOffers.row_eq 12 e ▸ PureOffers.ok12 e (by omega))
  · exact (PureOffers.row_eq 13 e ▸ PureOffers.ok13 e (by omega))
  · exact (PureOffers.row_eq 14 e ▸ PureOffers.ok14 e (by omega))
  · exact (PureOffers.row_eq 15 e ▸ PureOffers.ok15 e (by omega))
  · exact (PureOffers.row_eq 16 e ▸ PureOffers.ok16 e (by omega))
  · exact (PureOffers.row_eq 17 e ▸ PureOffers.ok17 e (by omega))
  · exact (PureOffers.row_eq 18 e ▸ PureOffers.ok18 e (by omega))
theorem one_price {r e t cost : ℕ} (hr : 1≤r) (hR : r≤18) (hY : r+e≤76)
    (left : r+e≤t) (top : t≤9352)
    (hraw : cost≤rowRaw r e (t-(r+e)))
    (hwin : ∀i, valid (bank i) r e t t → cost≤(bank i).fee) :
    cost≤oneUnits r e ((t-(r+e))/100)*10000000000000 :=
  one_price_of_row (all_rows r e hr hR hY) left top hraw hwin
theorem singleton_price {r e t cost : ℕ} (hr : 1≤r) (hR : r≤18) (hY : r+e≤76)
    (left : r+e≤t) (top : t≤maxTotal r e)
    (hraw : cost≤rowRaw r e (t-(r+e)))
    (hwin : ∀i, valid (bank i) r e t t → cost≤(bank i).fee) : cost≤budget r e t :=
  singleton_price_of_row (all_rows r e hr hR hY) left top hr hraw hwin
#print axioms one_price
#print axioms singleton_price
end Koala6836.Offers
