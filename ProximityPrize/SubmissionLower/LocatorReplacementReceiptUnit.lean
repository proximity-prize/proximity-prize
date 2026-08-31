import ProximityPrize.SubmissionLower.LocatorReplacementReceiptUnitBarrier07
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_unit:∀ c:UnitCell,Receipt (Sum.inr (Sum.inr c)):=by
  intro c
  rcases c with ⟨p,ti⟩
  fin_cases ti
  · exact receipt_unit_ti_0 p
  · exact receipt_unit_ti_1 p
  · exact receipt_unit_ti_2 p
  · exact receipt_unit_ti_3 p
  · exact receipt_unit_ti_4 p
  · exact receipt_unit_ti_5 p
  · exact receipt_unit_ti_6 p
  · exact receipt_unit_ti_7 p
  · exact receipt_unit_ti_8 p
  · exact receipt_unit_ti_9 p
  · exact receipt_unit_ti_10 p
  · exact receipt_unit_ti_11 p
  · exact receipt_unit_ti_12 p
  · exact receipt_unit_ti_13 p
  · exact receipt_unit_ti_14 p
  · exact receipt_unit_ti_15 p
  · exact receipt_unit_ti_16 p
  · exact receipt_unit_ti_17 p
  · exact receipt_unit_ti_18 p
  · exact receipt_unit_ti_19 p
  · exact receipt_unit_ti_20 p
  · exact receipt_unit_ti_21 p
  · exact receipt_unit_ti_22 p
  · exact receipt_unit_ti_23 p
  · exact receipt_unit_ti_24 p
  · exact receipt_unit_ti_25 p
  · exact receipt_unit_ti_26 p
  · exact receipt_unit_ti_27 p
  · exact receipt_unit_ti_28 p
  · exact receipt_unit_ti_29 p
  · exact receipt_unit_ti_30 p
  · exact receipt_unit_ti_31 p

end ProximityPrize.SubmissionLower.LocatorReplacementData
