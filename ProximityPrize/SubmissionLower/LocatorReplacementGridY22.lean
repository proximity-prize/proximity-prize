import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- The new endpoint strip created when the common Y cap rises from 88 to 89. -/
private theorem receipt_y_22_fixed_all :
    ∀ ri : Fin 19, FixedYReceipt ri ⟨22, by decide⟩ 0 24 := by
  decide +kernel

theorem receipt_y_22 (ri : Fin 19) : RowBandReceipt ri 22 23 :=
  fixedYReceipt_to_rowBand ri ⟨22, by decide⟩
    (receipt_y_22_fixed_all ri)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
