import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Band05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- A rectangular coarse-Y/coarse-T part of a slope-row receipt. -/
def RowTileReceipt (ri : Fin 18) (ylo yhi tlo thi : ℕ) : Prop :=
  ∀ (cy : Fin 22), ylo ≤ cy.val → cy.val < yhi →
    ∀ (ct : Fin 22), tlo ≤ ct.val → ct.val < thi →
      let coarse : CoarseCell := (ri, cy, ct)
      HardCoarse coarse →
        ∀ (yi ti : Fin 4),
          ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
            ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
              (unitBoxAt coarse yi ti ui).ordinaryFits ∨
                ∀ pi : Fin 4, (pointBoxAt coarse yi ti ui pi).valid →
                  (pointBoxAt coarse yi ti ui pi).ordinaryFits

instance (ri : Fin 18) (ylo yhi tlo thi : ℕ) :
    Decidable (RowTileReceipt ri ylo yhi tlo thi) := by
  unfold RowTileReceipt
  infer_instance

theorem receipt_row_06_band_06_t_00 : RowTileReceipt 6 8 9 0 4 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
