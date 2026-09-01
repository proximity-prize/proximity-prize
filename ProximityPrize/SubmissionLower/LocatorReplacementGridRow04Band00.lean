import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- The part of a slope-row receipt in a half-open coarse-Y interval. -/
def RowBandReceipt (ri : Fin 18) (lo hi : ℕ) : Prop :=
  ∀ (cy : Fin 21), lo ≤ cy.val → cy.val < hi → ∀ (ct : Fin 22),
    let coarse : CoarseCell := (ri, cy, ct)
    HardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) (lo hi : ℕ) : Decidable (RowBandReceipt ri lo hi) := by
  unfold RowBandReceipt
  infer_instance

theorem receipt_row_04_band_00 : RowBandReceipt 4 0 7 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
